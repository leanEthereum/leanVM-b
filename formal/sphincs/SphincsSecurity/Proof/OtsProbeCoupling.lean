import SphincsSecurity.Proof.OtsProbeTrace
import SphincsSecurity.Proof.FtsProbeProbability

/-!
# Retained one-time game coupling

The ordinary side of the split probing oracle is exactly the real lazy random oracle. This module
packages that distributional identity as the relational kernel used by the retained-game lift.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def RawOrdinaryResultRel :
    LazyRevealProbe.RawResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done _ _ (value, cache), ordinaryResult =>
      ordinaryResult = (value, ordinaryQueryCache cache)

def RawOrdinaryResultRelAt
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.RawResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done finalState remaining (value, cache), ordinaryResult =>
      finalState = state ∧ remaining = fuel ∧
        ordinaryResult = (value, ordinaryQueryCache cache)

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

theorem AnswersAgreeOnRun.queriedInputs_eq
    {f g : QueryImpl HashSpec Id} {computation : OracleComp HashSpec alpha}
    (hagrees : AnswersAgreeOnRun f g computation) :
    queriedInputs f computation = queriedInputs g computation :=
  hagrees.eval_eq_and_queriedInputs_eq.2

def CacheAnswersAgreeOnRun (cache : QueryCache HashSpec)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec alpha) : Prop :=
  ∀ input, input ∈ queriedInputs f computation →
    ∀ output, cache input = some output → f input = output

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

noncomputable def traceFallbackAnswer (cache : QueryCache HashSpec)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec alpha) :
    QueryImpl HashSpec Id := fun input =>
  if input ∈ queriedInputs f computation then f input else (cache input).getD 0

theorem cache_agreesWithFn_traceFallbackAnswer
    (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec alpha)
    (hagrees : CacheAnswersAgreeOnRun cache f computation) :
    cache.AgreesWithFn (traceFallbackAnswer cache f computation) := by
  intro input output hcached
  unfold traceFallbackAnswer
  split_ifs with hmem
  · exact hagrees input hmem output hcached
  · simp [hcached]

theorem answersAgreeOnRun_traceFallbackAnswer
    (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec alpha) :
    AnswersAgreeOnRun f (traceFallbackAnswer cache f computation) computation := by
  intro input hinput
  simp [traceFallbackAnswer, hinput]

set_option maxRecDepth 10000 in
theorem replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (computation : OracleComp HashSpec alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hf : CacheAnswersAgreeOnRun (ordinaryQueryCache finalCache) f computation)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter) computation).run cache))) :
    evalWithAnswerFn f computation = value ∧
      CachedRun (ordinaryQueryCache finalCache) f computation := by
  induction computation using OracleComp.inductionOn generalizing
      state cache finalState finalCache fuel remaining value with
  | pure result =>
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, by simp [CachedRun]⟩
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨queryRaw, hquery, hrest⟩ := hresult
      cases queryRaw with
      | stopped hit => simp at hrest
      | done queryState queryRemaining queryResult =>
          rcases queryResult with ⟨answer, queryCache⟩
          have hqueryProperty : ReturnsCachedOrdinary input
              (verifierHashImpl parameter input) :=
            returnsCachedOrdinary_verifierHashQuery parameter input
          have hcachedQuery : queryCache (.ordinary input) = some answer :=
            hqueryProperty state cache fuel queryState queryRemaining answer queryCache hquery
          have hcachedFinal : finalCache (.ordinary input) = some answer :=
            (ordinaryEntryPreservingImpl_verifierHashImpl parameter input).simulateQ
              (next answer) queryState queryCache queryRemaining finalState remaining value
                finalCache answer hcachedQuery hrest
          have hfinput : f input = answer := by
            apply hf input
            · rw [queriedInputs_query_bind]
              exact List.mem_cons_self
            · exact hcachedFinal
          have hfTail : CacheAnswersAgreeOnRun (ordinaryQueryCache finalCache) f
              (next answer) := by
            intro query hqueryTail output hcached
            apply hf query
            · rw [queriedInputs_query_bind, hfinput]
              exact List.mem_cons_of_mem input hqueryTail
            · exact hcached
          obtain ⟨htailEval, htailQueries⟩ := ih answer queryState finalState queryCache
            finalCache queryRemaining remaining value hfTail hrest
          constructor
          · rw [evalWithAnswerFn_bind,
              show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
                simulateQ_spec_query f input, hfinput]
            exact htailEval
          · intro other hother
            rw [queriedInputs_query_bind, hfinput] at hother
            simp only [List.mem_cons] at hother
            rcases hother with rfl | htail
            · simp [ordinaryQueryCache, hcachedFinal]
            · exact htailQueries other htail

theorem exists_right_mem_support_of_relTriple
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {left : OracleComp spec₁ alpha} {right : OracleComp spec₂ beta}
    {relation : alpha → beta → Prop}
    (hrel : RelTriple left right relation) {leftResult : alpha}
    (hleft : leftResult ∈ support left) :
    ∃ rightResult ∈ support right, relation leftResult rightResult := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel
  obtain ⟨coupling, hcoupled⟩ := hrel
  have hleftEval : leftResult ∈ support 𝒟[left] := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hleft ⊢
    exact hleft
  have hleftMapped : leftResult ∈ support (Prod.fst <$> coupling.1) := by
    rw [coupling.2.map_fst]
    exact hleftEval
  rw [support_map] at hleftMapped
  obtain ⟨jointResult, hjoint, hfst⟩ := hleftMapped
  rcases jointResult with ⟨coupledLeft, coupledRight⟩
  simp only at hfst
  subst coupledLeft
  refine ⟨coupledRight, ?_, hcoupled (leftResult, coupledRight) hjoint⟩
  have hrightMapped : coupledRight ∈ support (Prod.snd <$> coupling.1) := by
    rw [support_map]
    exact ⟨(leftResult, coupledRight), hjoint, rfl⟩
  rw [coupling.2.map_snd] at hrightMapped
  rw [mem_support_iff_evalDist_apply_ne_zero] at hrightMapped ⊢
  exact hrightMapped

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

theorem probingHashImpl_eq_ordinaryHashImpl_of_stable
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    probingHashImpl parameter input = ordinaryHashImpl input :=
  probingHashQuery_eq_splitHashQuery_of_stable parameter input hstable

theorem tableAnswer_eq_fallback_of_stable
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    tableAnswer parameter table fallback input = fallback input := by
  unfold tableAnswer
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

theorem stableCacheAgreesWithFn_tableAnswer
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (cache : SplitHashCache) :
    StableCacheAgreesWithFn parameter cache
      (tableAnswer parameter table (splitFallback cache)) := by
  intro input output hstable hcached
  rw [tableAnswer_eq_fallback_of_stable parameter table _ input hstable]
  simp [splitFallback, hcached]

theorem tableAnswer_realizes_otsPositions
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id) :
    ∀ position : Position, IsOtsPosition position →
      tableAnswer parameter table fallback
          (tableInput parameter table (.position position)) =
        table (.position position) := by
  intro position hposition
  exact tableAnswer_tableInput parameter table fallback position hposition

theorem mergedCache_extendTable_agreesWith_tableAnswer
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (base : Coordinate → HashOutput) (cache : SplitHashCache)
    (hconsistent : HiddenConsistent state cache) :
    (mergedCache parameter (extendTable state base) state.ensured cache).AgreesWithFn
      (tableAnswer parameter (extendTable state base) (splitFallback cache)) := by
  apply mergedCache_agreesWith_tableAnswer
  exact completedSplitHashCache_extendTable_consistent state cache base hconsistent

private theorem attach_flatMap_val {α β : Type*} (xs : List α) (g : α → List β) :
    xs.attach.flatMap (fun x => g x.1) = xs.flatMap g := by
  calc
    _ = (xs.attach.map Subtype.val).flatMap g := by rw [List.flatMap_map]
    _ = xs.flatMap g := by rw [List.attach_map_subtype_val]

private theorem positionDepth_wf :
    WellFounded (fun child parent : Position => child.depth < parent.depth) :=
  (measure Position.depth).wf

private noncomputable def completedRealizedPositionBody
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position)
    (recurse : ∀ child : Position, child.depth < position.depth → HashOutput) : HashOutput :=
  match state.values (.position position) with
  | some output => output
  | none =>
      show HashOutput from f (tweakableHashInput parameter position.domain <|
        match position with
        | .chain lay tree leafIdx chainIdx step =>
            if step.val = 0 then
              digestBytes (truncateHash ((state.values
                (.chainStart lay tree leafIdx chainIdx)).getD
                  (baseStarts lay tree leafIdx chainIdx)))
            else
              (Position.chain lay tree leafIdx chainIdx step).children.attach.flatMap fun child =>
                digestBytes (truncateHash (recurse child.1
                  (Position.depth_lt_of_mem_children child.2)))
        | .leaf lay tree leafIdx =>
            (Position.leaf lay tree leafIdx).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2)))
        | .node lay tree level nodeIdx =>
            (Position.node lay tree level nodeIdx).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2)))
        | .ftsLeaf index tree leafIdx =>
            (Position.ftsLeaf index tree leafIdx).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2)))
        | .ftsNode index tree level nodeIdx =>
            (Position.ftsNode index tree level nodeIdx).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2)))
        | .ftsRoots index =>
            (Position.ftsRoots index).children.attach.flatMap fun child =>
              digestBytes (truncateHash (recurse child.1
                (Position.depth_lt_of_mem_children child.2))))

noncomputable def completedRealizedPositionOutput
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Position → HashOutput :=
  positionDepth_wf.fix (completedRealizedPositionBody f parameter state baseStarts)

theorem completedRealizedPositionOutput_eq
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position) :
    completedRealizedPositionOutput f parameter state baseStarts position =
      completedRealizedPositionBody f parameter state baseStarts position
        (fun child _ => completedRealizedPositionOutput f parameter state baseStarts child) := by
  rw [completedRealizedPositionOutput, WellFounded.fix_eq]

noncomputable def completedRealizedTable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Coordinate → HashOutput
  | coordinate@(.chainStart lay tree leafIdx chainIdx) =>
      (state.values coordinate).getD (baseStarts lay tree leafIdx chainIdx)
  | .position position =>
      completedRealizedPositionOutput f parameter state baseStarts position

private theorem completedChildrenPayload_eq
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (positions : List Position) :
    (positions.map (tableValue (completedRealizedTable f parameter state baseStarts))).flatMap
        digestBytes =
      positions.attach.flatMap fun child =>
        digestBytes (truncateHash
          (completedRealizedPositionOutput f parameter state baseStarts child.1)) := by
  let payload := fun position : Position =>
    digestBytes (truncateHash
      (completedRealizedPositionOutput f parameter state baseStarts position))
  calc
    _ = positions.flatMap payload := by
      simp [payload, tableValue, completedRealizedTable, List.flatMap_map]
    _ = positions.attach.flatMap (fun child => payload child.1) :=
      (attach_flatMap_val positions payload).symm

theorem completedRealizedTable_of_value
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    completedRealizedTable f parameter state baseStarts coordinate = output := by
  cases coordinate with
  | chainStart => simp [completedRealizedTable, hvalue]
  | position position =>
      rw [completedRealizedTable, completedRealizedPositionOutput_eq]
      unfold completedRealizedPositionBody
      rw [hvalue]

theorem extendTable_completedRealizedTable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    extendTable state (completedRealizedTable f parameter state baseStarts) =
      completedRealizedTable f parameter state baseStarts := by
  funext coordinate
  unfold extendTable
  cases hvalue : state.values coordinate with
  | none => simp
  | some output =>
      rw [completedRealizedTable_of_value f parameter state baseStarts coordinate output hvalue]
      simp

theorem mergedCache_completedRealizedTable_agreesWith_tableAnswer
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (hconsistent : HiddenConsistent state cache) :
    (mergedCache parameter (completedRealizedTable f parameter state baseStarts)
      state.ensured cache).AgreesWithFn
        (tableAnswer parameter (completedRealizedTable f parameter state baseStarts)
          (splitFallback cache)) := by
  have hagrees := mergedCache_extendTable_agreesWith_tableAnswer parameter state
    (completedRealizedTable f parameter state baseStarts) cache hconsistent
  rw [extendTable_completedRealizedTable] at hagrees
  exact hagrees

theorem completedRealizedTable_realizes_of_missing
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position) (hmissing : state.values (.position position) = none) :
    f (tableInput parameter (completedRealizedTable f parameter state baseStarts)
        (.position position)) =
      completedRealizedTable f parameter state baseStarts (.position position) := by
  rw [completedRealizedTable, completedRealizedPositionOutput_eq]
  unfold completedRealizedPositionBody
  rw [hmissing]
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      simp only [tableInput, tablePayload, Position.domain, completedRealizedTable]
      rw [completedChildrenPayload_eq]
  | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
      simp only [tableInput, tablePayload, Position.domain]
      rw [completedChildrenPayload_eq]

theorem tableAnswer_completedRealizedTable_eq_of_missing
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position) (hots : IsOtsPosition position)
    (hmissing : state.values (.position position) = none) :
    tableAnswer parameter (completedRealizedTable f parameter state baseStarts) f
        (tableInput parameter (completedRealizedTable f parameter state baseStarts)
          (.position position)) =
      f (tableInput parameter (completedRealizedTable f parameter state baseStarts)
        (.position position)) := by
  rw [tableAnswer_tableInput parameter _ f position hots]
  exact (completedRealizedTable_realizes_of_missing f parameter state baseStarts position
    hmissing).symm

theorem tableAnswer_completedRealizedTable_eq_of_decoded_missing
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (state : LazyRevealProbe.State Coordinate)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (input : HashInput) (position : Position) (hots : IsOtsPosition position)
    (hposition : decodePosition? parameter input = some position)
    (hmissing : state.values (.position position) = none) :
    tableAnswer parameter (completedRealizedTable f parameter state baseStarts) f input =
      f input := by
  unfold tableAnswer
  rw [hposition]
  cases position with
  | chain | leaf | node =>
      simp only [tableAnswerDecoded]
      split_ifs with hexact
      · subst input
        exact (completedRealizedTable_realizes_of_missing f parameter state baseStarts _
          hmissing).symm
      · rfl
  | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots

noncomputable def retainedCompletionTable
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Coordinate → HashOutput :=
  completedRealizedTable (splitFallback cache) parameter state baseStarts

noncomputable def retainedCompletionAnswer
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    QueryImpl HashSpec Id :=
  tableAnswer parameter (retainedCompletionTable parameter state cache baseStarts)
    (splitFallback cache)

theorem tableOtsSecret_retainedCompletionTable
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    tableOtsSecret (retainedCompletionTable parameter state cache baseStarts)
        lay tree leafIdx chainIdx =
      truncateHash ((state.values (.chainStart lay tree leafIdx chainIdx)).getD
        (baseStarts lay tree leafIdx chainIdx)) := by
  rfl

theorem retainedCompletionAnswer_realizes
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    ∀ position : Position, IsOtsPosition position →
      retainedCompletionAnswer parameter state cache baseStarts
          (tableInput parameter (retainedCompletionTable parameter state cache baseStarts)
            (.position position)) =
        retainedCompletionTable parameter state cache baseStarts (.position position) := by
  exact tableAnswer_realizes_otsPositions parameter
    (retainedCompletionTable parameter state cache baseStarts) (splitFallback cache)

theorem stableCacheAgreesWithFn_retainedCompletionAnswer
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    StableCacheAgreesWithFn parameter cache
      (retainedCompletionAnswer parameter state cache baseStarts) := by
  exact stableCacheAgreesWithFn_tableAnswer parameter
    (retainedCompletionTable parameter state cache baseStarts) cache

theorem mergedCache_agreesWithFn_retainedCompletionAnswer
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (hconsistent : HiddenConsistent state cache) :
    (mergedCache parameter (retainedCompletionTable parameter state cache baseStarts)
      state.ensured cache).AgreesWithFn
        (retainedCompletionAnswer parameter state cache baseStarts) := by
  exact mergedCache_completedRealizedTable_agreesWith_tableAnswer
    (splitFallback cache) parameter state cache baseStarts hconsistent

theorem retainedCompletionAnswer_eq_fallback_of_decoded_missing
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (input : HashInput) (position : Position) (hots : IsOtsPosition position)
    (hposition : decodePosition? parameter input = some position)
    (hmissing : state.values (.position position) = none) :
    retainedCompletionAnswer parameter state cache baseStarts input = splitFallback cache input := by
  exact tableAnswer_completedRealizedTable_eq_of_decoded_missing
    (splitFallback cache) parameter state baseStarts input position hots hposition hmissing

theorem retainedCompletionAnswer_eq_fallback_or_exact_materialized
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (input : HashInput) :
    retainedCompletionAnswer parameter state cache baseStarts input = splitFallback cache input ∨
      ∃ position : Position,
        IsOtsPosition position ∧
          decodePosition? parameter input = some position ∧
          input = tableInput parameter
            (retainedCompletionTable parameter state cache baseStarts) (.position position) ∧
          state.values (.position position) ≠ none := by
  cases hposition : decodePosition? parameter input with
  | none =>
      left
      unfold retainedCompletionAnswer tableAnswer
      rw [hposition]
      rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          let position : Position := .chain lay tree leafIdx chainIdx step
          by_cases hexact : input = tableInput parameter
              (retainedCompletionTable parameter state cache baseStarts) (.position position)
          · by_cases hvalue : state.values (.position position) = none
            · left
              exact retainedCompletionAnswer_eq_fallback_of_decoded_missing parameter state
                cache baseStarts input position (by trivial) (by simp [position, hposition])
                  hvalue
            · right
              exact ⟨position, by trivial, by simp [position], hexact, hvalue⟩
          · left
            unfold retainedCompletionAnswer tableAnswer
            rw [hposition]
            simp only [tableAnswerDecoded]
            rw [if_neg hexact]
      | leaf lay tree leafIdx =>
          let position : Position := .leaf lay tree leafIdx
          by_cases hexact : input = tableInput parameter
              (retainedCompletionTable parameter state cache baseStarts) (.position position)
          · by_cases hvalue : state.values (.position position) = none
            · left
              exact retainedCompletionAnswer_eq_fallback_of_decoded_missing parameter state
                cache baseStarts input position (by trivial) (by simp [position, hposition])
                  hvalue
            · right
              exact ⟨position, by trivial, by simp [position], hexact, hvalue⟩
          · left
            unfold retainedCompletionAnswer tableAnswer
            rw [hposition]
            simp only [tableAnswerDecoded]
            rw [if_neg hexact]
      | node lay tree level nodeIdx =>
          let position : Position := .node lay tree level nodeIdx
          by_cases hexact : input = tableInput parameter
              (retainedCompletionTable parameter state cache baseStarts) (.position position)
          · by_cases hvalue : state.values (.position position) = none
            · left
              exact retainedCompletionAnswer_eq_fallback_of_decoded_missing parameter state
                cache baseStarts input position (by trivial) (by simp [position, hposition])
                  hvalue
            · right
              exact ⟨position, by trivial, by simp [position], hexact, hvalue⟩
          · left
            unfold retainedCompletionAnswer tableAnswer
            rw [hposition]
            simp only [tableAnswerDecoded]
            rw [if_neg hexact]
      | ftsLeaf | ftsNode | ftsRoots =>
          left
          unfold retainedCompletionAnswer tableAnswer
          rw [hposition]
          rfl

def ExactMaterializedCacheConsistent
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) : Prop :=
  ∀ (input : HashInput) (position : Position) (output : HashOutput),
    IsOtsPosition position →
    decodePosition? parameter input = some position →
    input = tableInput parameter table (.position position) →
    state.values (.position position) ≠ none →
    cache (.ordinary input) = some output → output = table (.position position)

def TraceExactMaterializedCacheConsistent
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec alpha) : Prop :=
  ∀ (input : HashInput), input ∈ queriedInputs f computation →
    ∀ (position : Position) (output : HashOutput),
      IsOtsPosition position →
      decodePosition? parameter input = some position →
      input = tableInput parameter table (.position position) →
      state.values (.position position) ≠ none →
      cache (.ordinary input) = some output → output = table (.position position)

theorem cacheAnswersAgreeOnRun_retainedCompletionAnswer_of_trace_exact_materialized
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (computation : OracleComp HashSpec alpha)
    (hexact : TraceExactMaterializedCacheConsistent parameter
      (retainedCompletionTable parameter state cache baseStarts) state cache
      (retainedCompletionAnswer parameter state cache baseStarts) computation) :
    CacheAnswersAgreeOnRun (ordinaryQueryCache cache)
      (retainedCompletionAnswer parameter state cache baseStarts) computation := by
  intro input hquery output hcached
  rcases retainedCompletionAnswer_eq_fallback_or_exact_materialized parameter state cache
      baseStarts input with hfallback | ⟨position, hots, hposition, hinput, hvalue⟩
  · rw [hfallback]
    change cache (.ordinary input) = some output at hcached
    simp [splitFallback, hcached]
  · rw [hinput, retainedCompletionAnswer_realizes parameter state cache baseStarts position hots]
    change cache (.ordinary input) = some output at hcached
    exact (hexact input hquery position output hots hposition hinput hvalue hcached).symm

theorem traceExactMaterializedCacheConsistent_of_cacheAnswersAgreeOnRun
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (computation : OracleComp HashSpec alpha)
    (hagrees : CacheAnswersAgreeOnRun (ordinaryQueryCache cache)
      (retainedCompletionAnswer parameter state cache baseStarts) computation) :
    TraceExactMaterializedCacheConsistent parameter
      (retainedCompletionTable parameter state cache baseStarts) state cache
      (retainedCompletionAnswer parameter state cache baseStarts) computation := by
  intro input hquery position output hots _hposition hinput _hvalue hcached
  have hcached' : ordinaryQueryCache cache input = some output := hcached
  have hanswer := hagrees input hquery output hcached'
  rw [hinput, retainedCompletionAnswer_realizes parameter state cache baseStarts position hots]
    at hanswer
  exact hanswer.symm

theorem cacheAnswersAgreeOnRun_retainedCompletionAnswer_iff
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (computation : OracleComp HashSpec alpha) :
    CacheAnswersAgreeOnRun (ordinaryQueryCache cache)
        (retainedCompletionAnswer parameter state cache baseStarts) computation ↔
      TraceExactMaterializedCacheConsistent parameter
        (retainedCompletionTable parameter state cache baseStarts) state cache
        (retainedCompletionAnswer parameter state cache baseStarts) computation := by
  constructor
  · exact traceExactMaterializedCacheConsistent_of_cacheAnswersAgreeOnRun parameter state
      cache baseStarts computation
  · exact cacheAnswersAgreeOnRun_retainedCompletionAnswer_of_trace_exact_materialized
      parameter state cache baseStarts computation

theorem ordinaryQueryCache_agreesWithFn_retainedCompletionAnswer_of_exact_materialized
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (hexact : ExactMaterializedCacheConsistent parameter
      (retainedCompletionTable parameter state cache baseStarts) state cache) :
    (ordinaryQueryCache cache).AgreesWithFn
      (retainedCompletionAnswer parameter state cache baseStarts) := by
  intro input output hcached
  rcases retainedCompletionAnswer_eq_fallback_or_exact_materialized parameter state cache
      baseStarts input with hfallback | ⟨position, hots, hposition, hinput, hvalue⟩
  · rw [hfallback]
    change cache (.ordinary input) = some output at hcached
    simp [splitFallback, hcached]
  · rw [hinput, retainedCompletionAnswer_realizes parameter state cache baseStarts position hots]
    change cache (.ordinary input) = some output at hcached
    exact (hexact input position output hots hposition hinput hvalue hcached).symm

theorem exactMaterializedCacheConsistent_of_ordinaryQueryCache_agreesWithFn
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (hagrees : (ordinaryQueryCache cache).AgreesWithFn
      (retainedCompletionAnswer parameter state cache baseStarts)) :
    ExactMaterializedCacheConsistent parameter
      (retainedCompletionTable parameter state cache baseStarts) state cache := by
  intro input position output hots _hposition hinput _hvalue hcached
  have hcached' : ordinaryQueryCache cache input = some output := hcached
  have hanswer := hagrees hcached'
  rw [hinput, retainedCompletionAnswer_realizes parameter state cache baseStarts position hots]
    at hanswer
  exact hanswer.symm

theorem ordinaryQueryCache_agreesWithFn_retainedCompletionAnswer_iff
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    (ordinaryQueryCache cache).AgreesWithFn
        (retainedCompletionAnswer parameter state cache baseStarts) ↔
      ExactMaterializedCacheConsistent parameter
        (retainedCompletionTable parameter state cache baseStarts) state cache := by
  constructor
  · exact exactMaterializedCacheConsistent_of_ordinaryQueryCache_agreesWithFn parameter state
      cache baseStarts
  · exact ordinaryQueryCache_agreesWithFn_retainedCompletionAnswer_of_exact_materialized
      parameter state cache baseStarts

noncomputable def realizedOtsSecret
    (chainStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leafIdx chainIdx => truncateHash (chainStarts lay tree leafIdx chainIdx)

noncomputable def realizedTable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (chainStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput) :
    Coordinate → HashOutput
  | .chainStart lay tree leafIdx chainIdx => chainStarts lay tree leafIdx chainIdx
  | .position position =>
      f (honestInput f parameter (realizedOtsSecret chainStarts) (fun _ _ _ => 0) position)

theorem tableInput_realizedTable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (chainStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (position : Position) (hots : IsOtsPosition position) (hvalid : position.Valid) :
    f (tableInput parameter (realizedTable f parameter chainStarts) (.position position)) =
      realizedTable f parameter chainStarts (.position position) := by
  let table := realizedTable f parameter chainStarts
  let otsSecret := realizedOtsSecret chainStarts
  let ftsSecret : Index → FtsTree → FtsLeaf → Digest := fun _ _ _ => 0
  have hvalue (child : Position) :
      tableValue table child = honestValue f parameter otsSecret ftsSecret child := by
    simp [tableValue, table, realizedTable, honestValue, otsSecret, ftsSecret]
  have hpayload :
      tablePayload table position = honestPayload f parameter otsSecret ftsSecret position := by
    cases position with
    | chain lay tree leafIdx chainIdx step =>
        by_cases hstep : step.val = 0
        · simp [tablePayload, hstep, honestPayload, Concrete.honestChain_zero, table,
            realizedTable, otsSecret, realizedOtsSecret]
        · rw [tablePayload, if_neg hstep]
          rw [honestPayload_eq_slots (f := f) (parameter := parameter)
            (otsSecret := otsSecret) (ftsSecret := ftsSecret) hvalid]
          simp only [slots, hstep, if_false, childValues]
          rfl
    | leaf | node =>
        rw [honestPayload_eq_slots (f := f) (parameter := parameter)
          (otsSecret := otsSecret) (ftsSecret := ftsSecret) hvalid]
        simp only [tablePayload, slots, childValues]
        rfl
    | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots
  change f (tweakableHashInput parameter position.domain (tablePayload table position)) =
    f (honestInput f parameter otsSecret ftsSecret position)
  rw [hpayload]
  rfl

theorem mem_runRaw_peekCoordinate_of_value
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    LazyRevealProbe.RawResult.done state fuel
        (some (truncateHash output), cache) ∈ support
      (LazyRevealProbe.runRaw state fuel ((peekCoordinate coordinate).run cache)) := by
  change LazyRevealProbe.RawResult.done state fuel
      (some (truncateHash output), cache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun value =>
        pure (truncateHash <$> value, cache)))
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind]
  simp [hvalue, LazyRevealProbe.runRaw]

theorem runRaw_peekCoordinate_of_value
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (coordinate : Coordinate) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    LazyRevealProbe.runRaw state fuel ((peekCoordinate coordinate).run cache) =
      pure (.done state fuel (some (truncateHash output), cache)) := by
  change LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun value =>
        pure (truncateHash <$> value, cache)) = _
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind]
  simp [hvalue, LazyRevealProbe.runRaw]

theorem runRaw_peekCoordinate_of_none
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (coordinate : Coordinate)
    (hvalue : state.values coordinate = none) :
    LazyRevealProbe.runRaw state fuel ((peekCoordinate coordinate).run cache) =
      pure (.done state fuel (none, cache)) := by
  change LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.peekQuery coordinate >>= fun value =>
        pure (truncateHash <$> value, cache)) = _
  rw [LazyRevealProbe.peekQuery, LazyRevealProbe.runRaw_peek_query_bind]
  simp [hvalue, LazyRevealProbe.runRaw]

theorem mem_runRaw_peekPositionValues_of_values
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) : ∀ positions : List Position,
    (∀ position, position ∈ positions →
      state.values (.position position) = some (table (.position position))) →
    LazyRevealProbe.RawResult.done state fuel
        (some (positions.map (tableValue table)), cache) ∈ support
      (LazyRevealProbe.runRaw state fuel ((peekPositionValues positions).run cache))
  | [], _ => by simp [peekPositionValues, LazyRevealProbe.runRaw]
  | position :: remaining, hvalues => by
      rw [peekPositionValues, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff]
      refine ⟨.done state fuel
        (some (tableValue table position), cache), ?_, ?_⟩
      · exact mem_runRaw_peekCoordinate_of_value state cache fuel (.position position)
          (table (.position position)) (hvalues position (by simp))
      · simp only
        rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff]
        refine ⟨.done state fuel
          (some (remaining.map (tableValue table)), cache), ?_, ?_⟩
        · exact mem_runRaw_peekPositionValues_of_values table state cache fuel remaining
            (fun other hother => hvalues other (by simp [hother]))
        · simp [LazyRevealProbe.runRaw]

theorem runRaw_peekPositionValues_of_values
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) : ∀ positions : List Position,
    (∀ position, position ∈ positions →
      state.values (.position position) = some (table (.position position))) →
    LazyRevealProbe.runRaw state fuel ((peekPositionValues positions).run cache) =
      pure (.done state fuel (some (positions.map (tableValue table)), cache))
  | [], _ => by simp [peekPositionValues, LazyRevealProbe.runRaw]
  | position :: remaining, hvalues => by
      rw [peekPositionValues, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_value state cache fuel (.position position)
          (table (.position position)) (hvalues position (by simp))]
      simp only [pure_bind]
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekPositionValues_of_values table state cache fuel remaining
          (fun other hother => hvalues other (by simp [hother]))]
      simp [LazyRevealProbe.runRaw, tableValue]

theorem runRaw_peekPositionValues_of_prefix_values_of_missing
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) (prior remaining : List Position)
    (position : Position)
    (hvalues : ∀ other, other ∈ prior →
      state.values (.position other) = some (table (.position other)))
    (hmissing : state.values (.position position) = none) :
    LazyRevealProbe.runRaw state fuel
        ((peekPositionValues (prior ++ position :: remaining)).run cache) =
      pure (.done state fuel (none, cache)) := by
  induction prior with
  | nil =>
      rw [List.nil_append, peekPositionValues, StateT.run_bind,
        LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_none state cache fuel (.position position) hmissing,
        pure_bind]
      simp [LazyRevealProbe.runRaw]
  | cons head tail ih =>
      rw [List.cons_append, peekPositionValues, StateT.run_bind,
        LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_value state cache fuel (.position head)
          (table (.position head)) (hvalues head (by simp))]
      simp only [pure_bind]
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
        ih (fun other hother => hvalues other (by simp [hother])), pure_bind]
      simp [LazyRevealProbe.runRaw]

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

theorem slotDigest_tableInput_node_child
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) (child : Position)
    (hchild : child ∈ (Position.node lay tree level nodeIdx).children) :
    slotDigest ((Position.node lay tree level nodeIdx).children.idxOf child)
        (tableInput parameter table
          (.position (.node lay tree level nodeIdx))) =
      truncateHash (table (.position child)) := by
  let children := (Position.node lay tree level nodeIdx).children
  have hidx : children.idxOf child < children.length :=
    List.idxOf_lt_length_iff.mpr hchild
  change slotDigest (children.idxOf child)
      (tweakableHashInput parameter (Position.node lay tree level nodeIdx).domain
        ((children.map (tableValue table)).flatMap digestBytes)) = _
  rw [slotDigest_flatMap parameter (Position.node lay tree level nodeIdx).domain
    (children.map (tableValue table)) (children.idxOf child) (by simpa using hidx)]
  simp [List.getElem_idxOf hidx, tableValue]

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

theorem slotDigest_tableInput_leaf_child
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (child : Position)
    (hchild : child ∈ (Position.leaf lay tree leafIdx).children) :
    slotDigest ((Position.leaf lay tree leafIdx).children.idxOf child)
        (tableInput parameter table (.position (.leaf lay tree leafIdx))) =
      truncateHash (table (.position child)) := by
  let children := (Position.leaf lay tree leafIdx).children
  have hidx : children.idxOf child < children.length :=
    List.idxOf_lt_length_iff.mpr hchild
  change slotDigest (children.idxOf child)
      (tweakableHashInput parameter (Position.leaf lay tree leafIdx).domain
        ((children.map (tableValue table)).flatMap digestBytes)) = _
  rw [slotDigest_flatMap parameter (Position.leaf lay tree leafIdx).domain
    (children.map (tableValue table)) (children.idxOf child) (by simpa using hidx)]
  simp [List.getElem_idxOf hidx, tableValue]

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

theorem TableInputAvailable.monoValues
    {table : Coordinate → HashOutput}
    {state finalState : LazyRevealProbe.State Coordinate} {coordinate : Coordinate}
    (havailable : TableInputAvailable table state coordinate)
    (hle : LazyRevealProbe.ValuesLE state finalState) :
    TableInputAvailable table finalState coordinate := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [TableInputAvailable] at havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [TableInputAvailable]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            exact hle _ _ (by simpa [TableInputAvailable, hzero] using havailable)
          · rw [if_neg hzero]
            have havailable' : ∀ child,
                child ∈ (Position.chain lay tree leafIdx chainIdx step).children →
                  state.values (.position child) = some (table (.position child)) := by
              simpa [TableInputAvailable, hzero] using havailable
            intro child hchild
            exact hle _ _ (havailable' child hchild)
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          intro child hchild
          exact hle _ _ (havailable child hchild)

theorem runRaw_probeFirstMissingInputCoordinate_of_values
    (table : Coordinate → HashOutput) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    ∀ (slot : Nat) (coordinates : List Coordinate),
      (∀ coordinate, coordinate ∈ coordinates →
        state.values coordinate = some (table coordinate)) →
      LazyRevealProbe.runRaw state fuel
          ((probeFirstMissingInputCoordinate input slot coordinates).run cache) =
        pure (.done state fuel ((), cache))
  | _, [], _ => by simp [probeFirstMissingInputCoordinate, LazyRevealProbe.runRaw]
  | slot, coordinate :: remaining, hvalues => by
      rw [probeFirstMissingInputCoordinate, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_value state cache fuel coordinate (table coordinate)
          (hvalues coordinate (by simp))]
      simp only [pure_bind]
      exact runRaw_probeFirstMissingInputCoordinate_of_values table input state cache fuel
        (slot + 1) remaining (fun other hother => hvalues other (by simp [hother]))

set_option maxRecDepth 10000 in
theorem runRaw_probeFirstMissingInputCoordinate_of_prefix_values_of_missing
    (table : Coordinate → HashOutput) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel slot : Nat) (prior remaining : List Coordinate) (coordinate : Coordinate)
    (hvalues : ∀ other, other ∈ prior →
      state.values other = some (table other))
    (hmissing : state.values coordinate = none)
    (hnotRevealed : coordinate ∉ state.revealed) :
    LazyRevealProbe.runRaw state (fuel + 1)
        ((probeFirstMissingInputCoordinate input slot
          (prior ++ coordinate :: remaining)).run cache) =
      pure (.done
        (state.addPending coordinate (slotDigest (slot + prior.length) input)) fuel
        ((), cache)) := by
  induction prior generalizing slot with
  | nil =>
      rw [List.nil_append, probeFirstMissingInputCoordinate, StateT.run_bind,
        LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_none state cache (fuel + 1) coordinate hmissing,
        pure_bind]
      change LazyRevealProbe.runRaw state (fuel + 1)
          (LazyRevealProbe.probeQuery coordinate (slotDigest slot input) >>= fun result =>
            pure (result, cache)) = _
      rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind,
        show fuel + 1 = Nat.succ fuel by omega]
      simp [hnotRevealed, LazyRevealProbe.runRaw]
  | cons head tail ih =>
      rw [List.cons_append, probeFirstMissingInputCoordinate, StateT.run_bind,
        LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_value state cache (fuel + 1) head (table head)
          (hvalues head (by simp))]
      simp only [pure_bind]
      have htailValues : ∀ other, other ∈ tail →
          state.values other = some (table other) := by
        intro other hother
        exact hvalues other (by simp [hother])
      rw [ih (slot + 1) htailValues]
      congr 4
      simp only [List.length_cons]
      omega

set_option maxRecDepth 10000 in
theorem runRaw_probeFirstMissingInputCoordinate_zero_of_prefix_values_of_missing
    (table : Coordinate → HashOutput) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (slot : Nat) (prior remaining : List Coordinate) (coordinate : Coordinate)
    (hvalues : ∀ other, other ∈ prior →
      state.values other = some (table other))
    (hmissing : state.values coordinate = none) :
    LazyRevealProbe.runRaw state 0
        ((probeFirstMissingInputCoordinate input slot
          (prior ++ coordinate :: remaining)).run cache) =
      pure (.stopped false) := by
  induction prior generalizing slot with
  | nil =>
      rw [List.nil_append, probeFirstMissingInputCoordinate, StateT.run_bind,
        LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_none state cache 0 coordinate hmissing, pure_bind]
      change LazyRevealProbe.runRaw state 0
          (LazyRevealProbe.probeQuery coordinate (slotDigest slot input) >>= fun result =>
            pure (result, cache)) = _
      rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind]
  | cons head tail ih =>
      rw [List.cons_append, probeFirstMissingInputCoordinate, StateT.run_bind,
        LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_value state cache 0 head (table head)
          (hvalues head (by simp))]
      simp only [pure_bind]
      exact ih (slot + 1) (fun other hother => hvalues other (by simp [hother]))

theorem runRaw_peekTableInput_of_available
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (coordinate : Coordinate)
    (havailable : TableInputAvailable table state coordinate) :
    LazyRevealProbe.runRaw state fuel ((peekTableInput parameter coordinate).run cache) =
      pure (.done state fuel (some (tableInput parameter table coordinate), cache)) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [TableInputAvailable] at havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero, StateT.run_bind, LazyRevealProbe.runRaw_bind,
              runRaw_peekCoordinate_of_value state cache fuel
                (.chainStart lay tree leafIdx chainIdx)
                (table (.chainStart lay tree leafIdx chainIdx))
                (by simpa [TableInputAvailable, hzero] using havailable)]
            simp [LazyRevealProbe.runRaw, tableInput, tablePayload, hzero]
          · rw [if_neg hzero, StateT.run_bind, LazyRevealProbe.runRaw_bind,
              runRaw_peekPositionValues_of_values table state cache fuel _
                (by simpa [TableInputAvailable, hzero] using havailable)]
            simp [LazyRevealProbe.runRaw, tableInput, tablePayload, hzero]
      | leaf lay tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]
      | node lay tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]
      | ftsLeaf index tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsLeaf index tree leafIdx) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]
      | ftsNode index tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsNode index tree level nodeIdx) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]
      | ftsRoots index =>
          rw [peekTableInput.eq_3 parameter (.ftsRoots index) (by simp),
            StateT.run_bind, LazyRevealProbe.runRaw_bind,
            runRaw_peekPositionValues_of_values table state cache fuel _ havailable]
          simp [LazyRevealProbe.runRaw, tableInput, tablePayload]

theorem runRaw_peekTableInput_node_of_prefix_values_of_missing
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) (prior remaining : List Position)
    (child : Position)
    (hchildren : (Position.node lay tree level nodeIdx).children =
      prior ++ child :: remaining)
    (hvalues : ∀ other, other ∈ prior →
      state.values (.position other) = some (table (.position other)))
    (hmissing : state.values (.position child) = none) :
    LazyRevealProbe.runRaw state fuel
        ((peekTableInput parameter
          (.position (.node lay tree level nodeIdx))).run cache) =
      pure (.done state fuel (none, cache)) := by
  rw [peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp),
    hchildren, StateT.run_bind, LazyRevealProbe.runRaw_bind,
    runRaw_peekPositionValues_of_prefix_values_of_missing table state cache fuel prior
      remaining child hvalues hmissing, pure_bind]
  simp [LazyRevealProbe.runRaw]

set_option maxRecDepth 10000 in
theorem probingHashQuery_node_pending_of_prefix_values_of_missing
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remainingFuel : Nat)
    (prior remaining : List Position) (child : Position) (output : HashOutput)
    (hchildren : (Position.node lay tree level nodeIdx).children =
      prior ++ child :: remaining)
    (hvalues : ∀ other, other ∈ prior →
      state.values (.position other) = some (table (.position other)))
    (hmissing : state.values (.position child) = none)
    (hnotRevealed : .position child ∉ state.revealed)
    (hresult : LazyRevealProbe.RawResult.done finalState remainingFuel
        (output, finalCache) ∈ support
      (LazyRevealProbe.runRaw state (fuel + 1)
        ((probingHashQuery parameter
          (tableInput parameter table
            (.position (.node lay tree level nodeIdx)))).run cache))) :
    finalState = state.addPending (.position child)
        (truncateHash (table (.position child))) ∧
      remainingFuel = fuel := by
  let position : Position := .node lay tree level nodeIdx
  let input := tableInput parameter table (.position position)
  have hposition : decodePosition? parameter input = some position :=
    (decodePosition?_eq_some_iff parameter input position).2
      ⟨tablePayload table position, rfl⟩
  have hprobe : decodeProbe? parameter input = none := by
    apply decodeProbe?_tweakableHashInput_of_not_chain_leaf parameter position.domain
      (tablePayload table position) position.domain_inRange
    · intro otherLay otherTree otherLeaf otherChain otherStep heq
      simp [position, Position.domain] at heq
    · intro otherLay otherTree otherLeaf heq
      simp [position, Position.domain] at heq
  let priorCoordinates := prior.map Coordinate.position
  let remainingCoordinates := remaining.map Coordinate.position
  have hcoordinates : position.children.map Coordinate.position =
      priorCoordinates ++ .position child :: remainingCoordinates := by
    simp only [position, hchildren, priorCoordinates, remainingCoordinates, List.map_append,
      List.map_cons]
  have hcoordinateValues : ∀ coordinate, coordinate ∈ priorCoordinates →
      state.values coordinate = some (table coordinate) := by
    intro coordinate hcoordinate
    obtain ⟨other, hother, rfl⟩ := List.mem_map.1 hcoordinate
    exact hvalues other hother
  have hslot : prior.length < position.children.length := by
    simp [position, hchildren]
  have hcandidate : slotDigest prior.length input =
      truncateHash (table (.position child)) := by
    have hread := slotDigest_tableInput_node_getElem parameter table lay tree level nodeIdx
      prior.length (by simpa [position] using hslot)
    have hget : position.children[prior.length] = child := by
      simp [position, hchildren]
    simpa [input, position, hget] using hread
  have hscan :=
    runRaw_probeFirstMissingInputCoordinate_of_prefix_values_of_missing table input state cache
      fuel 0 priorCoordinates remainingCoordinates (.position child) hcoordinateValues hmissing
        hnotRevealed
  have hcandidateCoordinates : slotDigest (0 + priorCoordinates.length) input =
      truncateHash (table (.position child)) := by
    simpa [priorCoordinates] using hcandidate
  rw [hcandidateCoordinates] at hscan
  change LazyRevealProbe.RawResult.done finalState remainingFuel (output, finalCache) ∈ support
    (LazyRevealProbe.runRaw state (fuel + 1)
      ((probingHashQuery parameter input).run cache)) at hresult
  unfold probingHashQuery at hresult
  rw [hprobe, hposition] at hresult
  simp only [position] at hresult
  rw [hcoordinates, StateT.run_bind, LazyRevealProbe.runRaw_bind, hscan, pure_bind] at hresult
  let probeState := state.addPending (.position child)
    (truncateHash (table (.position child)))
  have hpeek := runRaw_peekTableInput_node_of_prefix_values_of_missing parameter table lay tree
    level nodeIdx probeState cache fuel prior remaining child hchildren (by
      intro other hother
      simpa [probeState, LazyRevealProbe.State.addPending] using hvalues other hother) (by
        simpa [probeState, LazyRevealProbe.State.addPending] using hmissing)
  change LazyRevealProbe.RawResult.done finalState remainingFuel (output, finalCache) ∈ support
    (LazyRevealProbe.runRaw probeState fuel
      ((resolveKnownInput parameter (.position position) input).run cache)) at hresult
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, hpeek, pure_bind] at hresult
  have hprojection := mem_runRaw_splitHashQuery_ordinary_projects input probeState finalState
    cache finalCache fuel remainingFuel output hresult
  exact ⟨hprojection.1, hprojection.2.1⟩

set_option maxRecDepth 10000 in
theorem runRaw_prepareLeafInputProbe_of_prefix_values_of_missing
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (candidate : Probe)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (prior remaining : List Position) (child : Position)
    (hdecode : decodeProbe? parameter
      (tableInput parameter table (.position (.leaf lay tree leafIdx))) = some candidate)
    (hchildren : (Position.leaf lay tree leafIdx).children =
      prior ++ child :: remaining)
    (hvalues : ∀ other, other ∈ prior →
      state.values (.position other) = some (table (.position other)))
    (hmissing : state.values (.position child) = none)
    (hnotRevealed : .position child ∉ state.revealed) :
    LazyRevealProbe.runRaw state (fuel + 1)
        ((prepareLeafInputProbe
          (tableInput parameter table (.position (.leaf lay tree leafIdx)))
          candidate lay tree leafIdx).run cache) =
      pure (.done
        (state.addPending (.position child) (truncateHash (table (.position child)))) fuel
        ((), cache)) := by
  let input := tableInput parameter table (.position (.leaf lay tree leafIdx))
  have hzero : 0 < (Position.leaf lay tree leafIdx).children.length := by
    simp [hchildren]
  have hcandidate := decodeProbe?_tableInput_leaf_eq parameter table lay tree leafIdx candidate
    hdecode
  have hfirst := leaf_children_getElem_zero lay tree leafIdx hzero
  cases prior with
  | nil =>
      have hfirstChild : (Position.leaf lay tree leafIdx).children[0] = child := by
        simp [hchildren]
      have hsource :
          (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
            Position.lastChainStep : Position) = child := by
        rw [← hfirstChild]
        exact hfirst.symm
      have hdigest : slotDigest 0 input =
          truncateHash (table (.position child)) := by
        have hread := slotDigest_tableInput_leaf_getElem parameter table lay tree leafIdx 0 hzero
        simpa [input, hfirstChild] using hread
      rw [hcandidate]
      unfold prepareLeafInputProbe
      rw [hsource, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_none state cache (fuel + 1) (.position child) hmissing,
        pure_bind]
      change LazyRevealProbe.runRaw state (fuel + 1)
          (LazyRevealProbe.probeQuery (.position child) (slotDigest 0 input) >>= fun result =>
            pure (result, cache)) = _
      rw [hdigest, LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind,
        show fuel + 1 = Nat.succ fuel by omega]
      simp [hnotRevealed, LazyRevealProbe.runRaw]
  | cons head tail =>
      have hfirstChild : (Position.leaf lay tree leafIdx).children[0] = head := by
        simp [hchildren]
      have hsource :
          (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
            Position.lastChainStep : Position) = head := by
        rw [← hfirstChild]
        exact hfirst.symm
      let priorCoordinates := (head :: tail).map Coordinate.position
      let remainingCoordinates := remaining.map Coordinate.position
      have hcoordinates : (Position.leaf lay tree leafIdx).children.map Coordinate.position =
          priorCoordinates ++ .position child :: remainingCoordinates := by
        simp only [hchildren, priorCoordinates, remainingCoordinates, List.map_append,
          List.map_cons]
      have hcoordinateValues : ∀ coordinate, coordinate ∈ priorCoordinates →
          state.values coordinate = some (table coordinate) := by
        intro coordinate hcoordinate
        obtain ⟨other, hother, rfl⟩ := List.mem_map.1 hcoordinate
        exact hvalues other hother
      have hscan :=
        runRaw_probeFirstMissingInputCoordinate_of_prefix_values_of_missing table input state cache
          fuel 0 priorCoordinates remainingCoordinates (.position child) hcoordinateValues hmissing
            hnotRevealed
      have hslot : (head :: tail).length <
          (Position.leaf lay tree leafIdx).children.length := by
        simp [hchildren]
      have hdigest : slotDigest (head :: tail).length input =
          truncateHash (table (.position child)) := by
        have hread := slotDigest_tableInput_leaf_getElem parameter table lay tree leafIdx
          (head :: tail).length hslot
        simpa [input, hchildren] using hread
      have hdigestCoordinates : slotDigest (0 + priorCoordinates.length) input =
          truncateHash (table (.position child)) := by
        simpa [priorCoordinates] using hdigest
      rw [hdigestCoordinates] at hscan
      rw [hcandidate]
      unfold prepareLeafInputProbe
      rw [hsource, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_value state cache (fuel + 1) (.position head)
          (table (.position head)) (hvalues head (by simp))]
      simp only [pure_bind]
      rw [hcoordinates, hscan]

set_option maxRecDepth 10000 in
theorem runRaw_prepareLeafInputProbe_zero_of_prefix_values_of_missing
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (candidate : Probe)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (prior remaining : List Position) (child : Position)
    (hdecode : decodeProbe? parameter
      (tableInput parameter table (.position (.leaf lay tree leafIdx))) = some candidate)
    (hchildren : (Position.leaf lay tree leafIdx).children =
      prior ++ child :: remaining)
    (hvalues : ∀ other, other ∈ prior →
      state.values (.position other) = some (table (.position other)))
    (hmissing : state.values (.position child) = none) :
    LazyRevealProbe.runRaw state 0
        ((prepareLeafInputProbe
          (tableInput parameter table (.position (.leaf lay tree leafIdx)))
          candidate lay tree leafIdx).run cache) =
      pure (.stopped false) := by
  let input := tableInput parameter table (.position (.leaf lay tree leafIdx))
  have hzero : 0 < (Position.leaf lay tree leafIdx).children.length := by
    simp [hchildren]
  have hcandidate := decodeProbe?_tableInput_leaf_eq parameter table lay tree leafIdx candidate
    hdecode
  have hfirst := leaf_children_getElem_zero lay tree leafIdx hzero
  cases prior with
  | nil =>
      have hfirstChild : (Position.leaf lay tree leafIdx).children[0] = child := by
        simp [hchildren]
      have hsource :
          (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
            Position.lastChainStep : Position) = child := by
        rw [← hfirstChild]
        exact hfirst.symm
      rw [hcandidate]
      unfold prepareLeafInputProbe
      rw [hsource, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_none state cache 0 (.position child) hmissing, pure_bind]
      change LazyRevealProbe.runRaw state 0
          (LazyRevealProbe.probeQuery (.position child) (slotDigest 0 input) >>= fun result =>
            pure (result, cache)) = _
      rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind]
  | cons head tail =>
      have hfirstChild : (Position.leaf lay tree leafIdx).children[0] = head := by
        simp [hchildren]
      have hsource :
          (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
            Position.lastChainStep : Position) = head := by
        rw [← hfirstChild]
        exact hfirst.symm
      let priorCoordinates := (head :: tail).map Coordinate.position
      let remainingCoordinates := remaining.map Coordinate.position
      have hcoordinates : (Position.leaf lay tree leafIdx).children.map Coordinate.position =
          priorCoordinates ++ .position child :: remainingCoordinates := by
        simp only [hchildren, priorCoordinates, remainingCoordinates, List.map_append,
          List.map_cons]
      have hcoordinateValues : ∀ coordinate, coordinate ∈ priorCoordinates →
          state.values coordinate = some (table coordinate) := by
        intro coordinate hcoordinate
        obtain ⟨other, hother, rfl⟩ := List.mem_map.1 hcoordinate
        exact hvalues other hother
      have hscan :=
        runRaw_probeFirstMissingInputCoordinate_zero_of_prefix_values_of_missing table input state
          cache 0 priorCoordinates remainingCoordinates (.position child) hcoordinateValues hmissing
      rw [hcandidate]
      unfold prepareLeafInputProbe
      rw [hsource, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        runRaw_peekCoordinate_of_value state cache 0 (.position head)
          (table (.position head)) (hvalues head (by simp))]
      simp only [pure_bind]
      rw [hcoordinates, hscan]

theorem runRaw_peekTableInput_leaf_of_prefix_values_of_missing
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat)
    (prior remaining : List Position) (child : Position)
    (hchildren : (Position.leaf lay tree leafIdx).children =
      prior ++ child :: remaining)
    (hvalues : ∀ other, other ∈ prior →
      state.values (.position other) = some (table (.position other)))
    (hmissing : state.values (.position child) = none) :
    LazyRevealProbe.runRaw state fuel
        ((peekTableInput parameter (.position (.leaf lay tree leafIdx))).run cache) =
      pure (.done state fuel (none, cache)) := by
  rw [peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp),
    hchildren, StateT.run_bind, LazyRevealProbe.runRaw_bind,
    runRaw_peekPositionValues_of_prefix_values_of_missing table state cache fuel prior
      remaining child hvalues hmissing, pure_bind]
  simp [LazyRevealProbe.runRaw]

set_option maxRecDepth 10000 in
theorem probingHashQuery_leaf_pending_of_prefix_values_of_missing
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remainingFuel : Nat)
    (prior remaining : List Position) (child : Position) (output : HashOutput)
    (hchildren : (Position.leaf lay tree leafIdx).children =
      prior ++ child :: remaining)
    (hvalues : ∀ other, other ∈ prior →
      state.values (.position other) = some (table (.position other)))
    (hmissing : state.values (.position child) = none)
    (hnotRevealed : .position child ∉ state.revealed)
    (hresult : LazyRevealProbe.RawResult.done finalState remainingFuel
        (output, finalCache) ∈ support
      (LazyRevealProbe.runRaw state (fuel + 1)
        ((probingHashQuery parameter
          (tableInput parameter table (.position (.leaf lay tree leafIdx)))).run cache))) :
    finalState = state.addPending (.position child)
        (truncateHash (table (.position child))) ∧
      remainingFuel = fuel := by
  let position : Position := .leaf lay tree leafIdx
  let input := tableInput parameter table (.position position)
  let candidate : Probe :=
    ⟨.position (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
      Position.lastChainStep), slotDigest 0 input⟩
  have hprobe : decodeProbe? parameter input = some candidate := by
    apply (decodeProbe?_eq_some_iff parameter input candidate).2
    simp only [candidate, Probe.MatchesInput]
    rw [dif_neg (by simp [Position.lastChainStep, chainLength, winternitzBits])]
    exact ⟨trivial, tablePayload table position, rfl, trivial⟩
  have hposition : decodePosition? parameter input = some position :=
    (decodePosition?_eq_some_iff parameter input position).2
      ⟨tablePayload table position, rfl⟩
  have hprepare := runRaw_prepareLeafInputProbe_of_prefix_values_of_missing parameter table lay
    tree leafIdx candidate state cache fuel prior remaining child (by simpa [input, position]
      using hprobe) hchildren hvalues hmissing hnotRevealed
  change LazyRevealProbe.RawResult.done finalState remainingFuel (output, finalCache) ∈ support
    (LazyRevealProbe.runRaw state (fuel + 1)
      ((probingHashQuery parameter input).run cache)) at hresult
  unfold probingHashQuery at hresult
  rw [hprobe, hposition] at hresult
  simp only [position] at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, hprepare, pure_bind] at hresult
  let probeState := state.addPending (.position child)
    (truncateHash (table (.position child)))
  have hpeek := runRaw_peekTableInput_leaf_of_prefix_values_of_missing parameter table lay tree
    leafIdx probeState cache fuel prior remaining child hchildren (by
      intro other hother
      simpa [probeState, LazyRevealProbe.State.addPending] using hvalues other hother) (by
        simpa [probeState, LazyRevealProbe.State.addPending] using hmissing)
  change LazyRevealProbe.RawResult.done finalState remainingFuel (output, finalCache) ∈ support
    (LazyRevealProbe.runRaw probeState fuel
      ((resolveKnownInput parameter (.position position) input).run cache)) at hresult
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, hpeek, pure_bind] at hresult
  have hprojection := mem_runRaw_splitHashQuery_ordinary_projects input probeState finalState
    cache finalCache fuel remainingFuel output hresult
  exact ⟨hprojection.1, hprojection.2.1⟩

theorem mem_runRaw_revealCoordinateOutput_value
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealCoordinateOutput coordinate).run cache))) :
    finalState.values coordinate = some output ∧
      finalCache (.hidden coordinate) = some output := by
  rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some cached =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hvalue, by simp [Function.update]⟩
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hrest⟩ := hresult
      by_cases hhit : state.hitAt coordinate sampled
      · rw [if_pos hhit] at hrest
        simp at hrest
      · rw [if_neg hhit] at hrest
        simp [LazyRevealProbe.runRaw] at hrest
        rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨by simp [LazyRevealProbe.State.materialize, Function.update],
          by simp [Function.update]⟩

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

theorem maskedOtsSignFrom_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) : ∀ attempts counter
      (state finalState : LazyRevealProbe.State Coordinate)
      (cache finalCache : SplitHashCache) (fuel remaining : Nat)
      (selectedCounter : Counter) (encoding : ChainIndex → Digit),
      StableCacheAgreesWithFn parameter finalCache f →
      LazyRevealProbe.RawResult.done finalState remaining
          (some (selectedCounter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          ((maskedOtsSignFrom parameter lay tree leafIdx message attempts counter).run cache)) →
      evalWithAnswerFn f
          (otsSignFrom parameter lay tree leafIdx secret message attempts counter) =
        some (selectedCounter, fun chainIdx =>
          honestChain f parameter lay tree leafIdx chainIdx (secret chainIdx)
            (encoding chainIdx).val)
  | 0, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, hf, hresult => by
      simp [maskedOtsSignFrom, LazyRevealProbe.runRaw] at hresult
  | attempts + 1, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, hf, hresult => by
      rw [maskedOtsSignFrom, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, hencode, hrest⟩ := hresult
      cases raw with
      | stopped hit => simp at hrest
      | done encodeState encodeRemaining encodeResult =>
          rcases encodeResult with ⟨encoded, encodeCache⟩
          simp only at hrest
          cases encoded with
          | none =>
              have hordinaryLE := ordinaryCacheIncreasing_maskedOtsSignFrom parameter lay tree
                leafIdx message attempts (counter + 1) encodeState encodeCache encodeRemaining
                  finalState remaining (some (selectedCounter, encoding)) finalCache hrest
              have hfEncode : StableCacheAgreesWithFn parameter encodeCache f :=
                fun input output hstable hcached => hf input output hstable
                  (hordinaryLE hcached)
              have hencoded := (replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
                state encodeState cache encodeCache fuel encodeRemaining none hfEncode
                  (queriesStable_encode f parameter lay tree leafIdx message
                    (BitVec.ofNat counterBits counter)) hencode).1
              rw [otsSignFrom, evalWithAnswerFn_bind, hencoded]
              exact maskedOtsSignFrom_some_honest_eval f parameter lay tree leafIdx secret message
                attempts (counter + 1) encodeState finalState encodeCache finalCache
                  encodeRemaining remaining selectedCounter encoding hf hrest
          | some selectedEncoding =>
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hrest
              obtain ⟨ensureRaw, hensure, hfinish⟩ := hrest
              cases ensureRaw with
              | stopped hit => simp at hfinish
              | done ensureState ensureRemaining ensureResult =>
                  rcases ensureResult with ⟨ensured, ensureCache⟩
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, hselected, rfl⟩
                  rcases hselected with ⟨hcounter, hencoding⟩
                  subst selectedCounter
                  subst encoding
                  have hordinaryLE := ordinaryCacheIncreasing_sequenceFin
                    (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
                      (selectedEncoding chainIdx))
                    (fun chainIdx =>
                      (splitCachePreserving_ensureChainPrefix lay tree leafIdx chainIdx
                        (selectedEncoding chainIdx)).ordinaryCacheIncreasing)
                    encodeState encodeCache encodeRemaining finalState remaining ensured finalCache
                      hensure
                  have hfEncode : StableCacheAgreesWithFn parameter encodeCache f :=
                    fun input output hstable hcached => hf input output hstable
                      (hordinaryLE hcached)
                  have hencoded := (replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                    (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
                    state encodeState cache encodeCache fuel encodeRemaining
                      (some selectedEncoding) hfEncode
                      (queriesStable_encode f parameter lay tree leafIdx message
                        (BitVec.ofNat counterBits counter)) hencode).1
                  rw [otsSignFrom, evalWithAnswerFn_bind, hencoded,
                    evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
                    evalWithAnswerFn_pure]
                  congr 2

theorem maskedOtsSign_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsSign parameter lay tree leafIdx message).run cache))) :
    evalWithAnswerFn f (otsSign parameter lay tree leafIdx secret message) =
      some (counter, fun chainIdx =>
        honestChain f parameter lay tree leafIdx chainIdx (secret chainIdx)
          (encoding chainIdx).val) := by
  exact maskedOtsSignFrom_some_honest_eval f parameter lay tree leafIdx secret message
    encodingAttemptLimit 0 state finalState cache finalCache fuel remaining counter encoding
      hf hresult

theorem maskedOtsLayerAfterMessage_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (lay : Layer)
    (secret : ChainIndex → Digest) (message actualMessage : Digest)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hmessage : message = actualMessage)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsLayerAfterMessage parameter index lay message).run cache))) :
    evalWithAnswerFn f
        (otsSign parameter lay (treeIndexAt index lay) (leafIndexAt index lay) secret
          actualMessage) =
      some (counter, fun chainIdx =>
        honestChain f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx (secret chainIdx) (encoding chainIdx).val) := by
  unfold maskedOtsLayerAfterMessage at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨otsRaw, hots, hafterOts⟩ := hresult
  cases otsRaw with
  | stopped hit => simp at hafterOts
  | done otsState otsRemaining otsResult =>
      rcases otsResult with ⟨part, otsCache⟩
      cases part with
      | none => simp [LazyRevealProbe.runRaw] at hafterOts
      | some selectedPart =>
          rcases selectedPart with ⟨selectedCounter, selectedEncoding⟩
          simp only at hafterOts
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterOts
          obtain ⟨pathRaw, hpath, hfinish⟩ := hafterOts
          cases pathRaw with
          | stopped hit => simp at hfinish
          | done pathState pathRemaining pathResult =>
              rcases pathResult with ⟨pathUnit, pathCache⟩
              have hpathCache := splitCachePreserving_ensureTreePath lay
                (treeIndexAt index lay) (leafIndexAt index lay) otsState otsCache otsRemaining
                  pathState pathRemaining pathUnit pathCache hpath
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, hpart, rfl⟩
              rcases hpart with ⟨hcounter, hencoding⟩
              subst selectedCounter
              subst selectedEncoding
              rw [hpathCache] at hf
              subst message
              exact maskedOtsSign_some_honest_eval f parameter lay
                (treeIndexAt index lay) (leafIndexAt index lay) secret actualMessage state
                  otsState cache otsCache fuel otsRemaining counter encoding hf hots

theorem maskedSignLayer_some_honest_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayer parameter ftsSecret index lay).run cache))) :
    evalWithAnswerFn f
        (otsSign parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay))
          (evalWithAnswerFn f
            (layerMessage
              (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay))) =
      some (counter, fun chainIdx =>
        honestChain f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx
          (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)
          (encoding chainIdx).val) := by
  unfold maskedSignLayer at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨messageRaw, hmessage, hafterMessage⟩ := hresult
  cases messageRaw with
  | stopped hit => simp at hafterMessage
  | done messageState messageRemaining messageResult =>
      rcases messageResult with ⟨message, messageCache⟩
      simp only at hafterMessage
      change LazyRevealProbe.RawResult.done finalState remaining
          (some (counter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw messageState messageRemaining
          ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache))
        at hafterMessage
      by_cases hbelow : lay.val + 1 < numLayers
      · let below : Layer := ⟨lay.val + 1, hbelow⟩
        have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
          ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)
            messageState finalState messageRemaining remaining
              (some (counter, encoding), finalCache) hafterMessage
        have hmessageActual := maskedLayerMessage_eq_actual_of_lt
          (f := f) (parameter := parameter) (root := root) (table := table)
          (ftsSecret := ftsSecret) (index := index) (lay := lay) (below := below)
          (hbelow := hbelow) (hbelowEq := rfl) (state := state)
          (messageState := messageState) (referenceState := finalState) (cache := cache)
          (messageCache := messageCache) (fuel := fuel) (messageRemaining := messageRemaining)
          (message := message) hvaluesLE htable hrealizes hmessage
        exact maskedOtsLayerAfterMessage_some_honest_eval f parameter index lay
          (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay)) message
          (evalWithAnswerFn f
            (layerMessage
              (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay))
          messageState finalState messageCache finalCache messageRemaining remaining counter
            encoding hf hmessageActual hafterMessage
      · have hordinaryLE := ordinaryCacheIncreasing_maskedSignLayerAfterMessage parameter index lay
          message messageState messageCache messageRemaining finalState remaining
            (some (counter, encoding)) finalCache hafterMessage
        have hfMessage : StableCacheAgreesWithFn parameter messageCache f :=
          fun input output hstable hcached => hf input output hstable (hordinaryLE hcached)
        have hmessageActual := maskedLayerMessage_eq_actual_of_not_lt f parameter root table
          ftsSecret index lay hbelow state messageState cache messageCache fuel messageRemaining
            message hfMessage hmessage
        exact maskedOtsLayerAfterMessage_some_honest_eval f parameter index lay
          (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay)) message
          (evalWithAnswerFn f
            (layerMessage
              (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay))
          messageState finalState messageCache finalCache messageRemaining remaining counter
            encoding hf hmessageActual hafterMessage

theorem evalWithAnswerFn_treePath_eq_table
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    evalWithAnswerFn f
        (treePath parameter lay tree (tableOtsSecret table lay tree) leafIdx) =
      fun level =>
        if level.val < layerHeight lay then
          match level.val with
          | 0 => truncateHash (table (.position (.leaf lay tree
              (leafOfNat (Nat.xor leafIdx.val 1)))))
          | current + 1 =>
              if hcurrent : current < maxLayerHeight then
                truncateHash (table (.position (.node lay tree ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor (leafIdx.val / 2 ^ (current + 1)) 1)))))
              else 0
        else 0 := by
  funext level
  simp only [treePath, evalWithAnswerFn_sequenceFin]
  by_cases hinLayer : level.val < layerHeight lay
  · rw [if_pos hinLayer, if_pos hinLayer]
    cases hlevelValue : level.val with
    | zero =>
        have hspan := FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val 0
          (by norm_num [maxLayerHeight]) leafIdx.isLt
        have hsibling : Nat.xor leafIdx.val 1 < 2 ^ maxLayerHeight := by
          simpa using hspan
        have hleafValue : (leafOfNat (Nat.xor leafIdx.val 1)).val =
            Nat.xor leafIdx.val 1 := by
          change Nat.xor leafIdx.val 1 % 2 ^ maxLayerHeight = Nat.xor leafIdx.val 1
          exact Nat.mod_eq_of_lt hsibling
        have hnode := honestNode_zero_eq_table f parameter table lay tree
          (leafOfNat (Nat.xor leafIdx.val 1)) hrealizes
        rw [hleafValue] at hnode
        simpa [honestNode, hlevelValue, tableValue] using hnode
    | succ current =>
        have hcurrent : current < maxLayerHeight := by
          have := layerHeight_le lay
          omega
        have hspan := FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val
          (current + 1) (by omega) leafIdx.isLt
        have hnode := honestNode_eq_table_succ f parameter table lay tree hrealizes current
          (Nat.xor (leafIdx.val / 2 ^ (current + 1)) 1) hcurrent hspan
        simpa [honestNode, hlevelValue, hcurrent, tableValue] using hnode
  · simp [hinLayer]

theorem honestChain_eq_table_chainValueCoordinate
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    honestChain f parameter lay tree leafIdx chainIdx
        (tableOtsSecret table lay tree leafIdx chainIdx) digit.val =
      truncateHash (table (chainValueCoordinate lay tree leafIdx chainIdx digit)) := by
  by_cases hzero : digit.val = 0
  · simp [chainValueCoordinate, hzero, honestChain_zero, tableOtsSecret]
  · have hstep : digit.val - 1 < chainLength - 1 := by
      have := digit.isLt
      omega
    have hchain := honestChain_eq_table_succ f parameter table lay tree leafIdx chainIdx
      hrealizes (digit.val - 1) hstep
    have hvalue : digit.val - 1 + 1 = digit.val := by omega
    rw [hvalue] at hchain
    simpa [chainValueCoordinate, hzero, tableValue] using hchain

theorem maskedSignLayer_and_reveal_eval
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (counter : Counter)
    (encoding : ChainIndex → Digit)
    (signState signFinalState : LazyRevealProbe.State Coordinate)
    (signCache signFinalCache : SplitHashCache) (signFuel signRemaining : Nat)
    (revealState revealFinalState : LazyRevealProbe.State Coordinate)
    (revealCache revealFinalCache : SplitHashCache) (revealFuel revealRemaining : Nat)
    (values : (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))
    (hf : StableCacheAgreesWithFn parameter signFinalCache f)
    (htableSign : ∀ coordinate output,
      signFinalState.values coordinate = some output → output = table coordinate)
    (htableReveal : ∀ coordinate output,
      revealFinalState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hsign : LazyRevealProbe.RawResult.done signFinalState signRemaining
        (some (counter, encoding), signFinalCache) ∈ support
      (LazyRevealProbe.runRaw signState signFuel
        ((maskedSignLayer parameter ftsSecret index lay).run signCache)))
    (hreveal : LazyRevealProbe.RawResult.done revealFinalState revealRemaining
        (values, revealFinalCache) ∈ support
      (LazyRevealProbe.runRaw revealState revealFuel
        ((revealLayerValues index lay encoding).run revealCache))) :
    evalWithAnswerFn f
        (signLayer
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay) =
      some (counter, values.1, values.2) := by
  have hots := maskedSignLayer_some_honest_eval f parameter root table ftsSecret index lay
    signState signFinalState signCache signFinalCache signFuel signRemaining counter encoding hf
      htableSign hrealizes hsign
  have hotsTable : evalWithAnswerFn f
      (otsSign parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay))
        (evalWithAnswerFn f
          (layerMessage
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay))) =
    some (counter, fun chainIdx => truncateHash (table
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx)))) := by
    rw [hots]
    congr 2
    funext chainIdx
    exact honestChain_eq_table_chainValueCoordinate f parameter table lay
      (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx) hrealizes
  have hpathTable := evalWithAnswerFn_treePath_eq_table f parameter table lay
    (treeIndexAt index lay) (leafIndexAt index lay) hrealizes
  have hrevealedTable := revealLayerValues_eq_table table index lay encoding revealState
    revealFinalState revealCache revealFinalCache revealFuel revealRemaining values htableReveal
      hreveal
  rw [signLayer, evalWithAnswerFn_bind, evalWithAnswerFn_bind, hotsTable,
    evalWithAnswerFn_bind, hpathTable, evalWithAnswerFn_pure, hrevealedTable.1,
    hrevealedTable.2]

theorem mergedCache_tableInput_ne_none_of_ensured
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (position : Position) (hots : IsOtsPosition position)
    (hensured : Coordinate.position position ∈ state.ensured) :
    mergedCache parameter table state.ensured cache
        (tableInput parameter table (.position position)) ≠ none := by
  rw [mergedCache_tableInput parameter table state.ensured cache position hots]
  cases hhidden : cache (.hidden (.position position)) <;>
    simp [completedSplitHashCache, hhidden, hensured]

theorem mergedCache_eq_ordinary_of_stable
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ensured : Finset Coordinate) (cache : SplitHashCache) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    mergedCache parameter table ensured cache input = cache (.ordinary input) := by
  rcases hstable with ⟨_, hstable⟩
  unfold mergedCache
  cases hposition : decodePosition? parameter input with
  | none => rfl
  | some position =>
      have hnots := hstable position hposition
      cases position <;> simp [mergeDecodedPosition, IsOtsPosition] at hnots ⊢

theorem mergedCache_eq_ordinary_or_exact
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ensured : Finset Coordinate) (cache : SplitHashCache) (input : HashInput) :
    mergedCache parameter table ensured cache input = cache (.ordinary input) ∨
      ∃ position : Position, IsOtsPosition position ∧
        input = tableInput parameter table (.position position) := by
  unfold mergedCache
  cases hposition : decodePosition? parameter input with
  | none => exact Or.inl rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hexact : input = tableInput parameter table
              (.position (.chain lay tree leafIdx chainIdx step))
          · refine Or.inr ⟨.chain lay tree leafIdx chainIdx step, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [mergeDecodedPosition, hexact])
      | leaf lay tree leafIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.leaf lay tree leafIdx))
          · refine Or.inr ⟨.leaf lay tree leafIdx, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [mergeDecodedPosition, hexact])
      | node lay tree level nodeIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.node lay tree level nodeIdx))
          · refine Or.inr ⟨.node lay tree level nodeIdx, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [mergeDecodedPosition, hexact])
      | ftsLeaf | ftsNode | ftsRoots => exact Or.inl (by simp [mergeDecodedPosition])

theorem tableAnswer_eq_fallback_or_exact
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (fallback : QueryImpl HashSpec Id) (input : HashInput) :
    tableAnswer parameter table fallback input = fallback input ∨
      ∃ position : Position, IsOtsPosition position ∧
        input = tableInput parameter table (.position position) := by
  unfold tableAnswer
  cases hposition : decodePosition? parameter input with
  | none => exact Or.inl rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hexact : input = tableInput parameter table
              (.position (.chain lay tree leafIdx chainIdx step))
          · refine Or.inr ⟨.chain lay tree leafIdx chainIdx step, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [tableAnswerDecoded, hexact])
      | leaf lay tree leafIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.leaf lay tree leafIdx))
          · refine Or.inr ⟨.leaf lay tree leafIdx, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [tableAnswerDecoded, hexact])
      | node lay tree level nodeIdx =>
          by_cases hexact : input = tableInput parameter table
              (.position (.node lay tree level nodeIdx))
          · refine Or.inr ⟨.node lay tree level nodeIdx, ?_, hexact⟩
            exact True.intro
          · exact Or.inl (by simp [tableAnswerDecoded, hexact])
      | ftsLeaf | ftsNode | ftsRoots => exact Or.inl (by simp [tableAnswerDecoded])

theorem cachedRun_mergedCache_of_stable
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (computation : OracleComp HashSpec alpha)
    (hstable : QueriesStable parameter f computation)
    (hrun : CachedRun (ordinaryQueryCache cache) f computation) :
    CachedRun (mergedCache parameter table state.ensured cache) f computation := by
  intro input hinput
  rw [mergedCache_eq_ordinary_of_stable parameter table state.ensured cache input
    (hstable input hinput)]
  exact hrun input hinput

def StableOrdinaryCacheLE (parameter : PublicParameter)
    (initial final : SplitHashCache) : Prop :=
  ∀ input output, StableOrdinaryInput parameter input →
    initial (.ordinary input) = some output → final (.ordinary input) = some output

theorem StableOrdinaryCacheLE.refl (parameter : PublicParameter) (cache : SplitHashCache) :
    StableOrdinaryCacheLE parameter cache cache := by
  intro input output hstable hcached
  exact hcached

theorem StableOrdinaryCacheLE.trans
    {parameter : PublicParameter} {first second third : SplitHashCache}
    (hfirst : StableOrdinaryCacheLE parameter first second)
    (hsecond : StableOrdinaryCacheLE parameter second third) :
    StableOrdinaryCacheLE parameter first third := by
  intro input output hstable hcached
  exact hsecond input output hstable (hfirst input output hstable hcached)

theorem StableOrdinaryCacheLE.of_le
    {parameter : PublicParameter} {initial final : SplitHashCache}
    (hle : ordinaryQueryCache initial ≤ ordinaryQueryCache final) :
    StableOrdinaryCacheLE parameter initial final := by
  intro input output hstable hcached
  exact hle hcached

theorem CachedRun.mono_stableOrdinary
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {initial final : SplitHashCache} {computation : OracleComp HashSpec alpha}
    (hstable : QueriesStable parameter f computation)
    (hle : StableOrdinaryCacheLE parameter initial final)
    (hrun : CachedRun (ordinaryQueryCache initial) f computation) :
    CachedRun (ordinaryQueryCache final) f computation := by
  intro input hinput
  obtain ⟨output, hcached⟩ := Option.ne_none_iff_exists'.mp (hrun input hinput)
  change initial (.ordinary input) = some output at hcached
  change final (.ordinary input) ≠ none
  rw [hle input output (hstable input hinput) hcached]
  simp

theorem cachedRun_chainWalk_of_ensured
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    ∀ steps : Nat,
      (∀ step : ChainStep, step.val < steps →
        Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ state.ensured) →
      CachedRun (mergedCache parameter table state.ensured cache) f
        (chainWalk parameter lay tree leafIdx chainIdx 0 steps
          (tableOtsSecret table lay tree leafIdx chainIdx))
  | 0, _ => CachedRun.pure _ _ _
  | steps + 1, hensured => by
      rw [chainWalk]
      apply CachedRun.bind
      · exact cachedRun_chainWalk_of_ensured f parameter table state cache lay tree leafIdx
          chainIdx hrealizes steps (fun step hstep => hensured step (by omega))
      · split_ifs with hstep
        · intro input hinput
          simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
          subst input
          have hstep' : steps < chainLength - 1 := by omega
          let position : ChainStep := ⟨steps, hstep'⟩
          have hinput :
              tweakableHashInput parameter (.chain lay tree leafIdx chainIdx position)
                  (digestBytes (honestChain f parameter lay tree leafIdx chainIdx
                    (tableOtsSecret table lay tree leafIdx chainIdx) steps)) =
                tableInput parameter table
                  (.position (.chain lay tree leafIdx chainIdx position)) := by
            cases steps with
            | zero =>
                simp [honestChain_zero, tableInput, tablePayload, tableOtsSecret,
                  Position.domain, position]
            | succ previous =>
                have hprevious : previous < chainLength - 1 := by omega
                rw [honestChain_eq_table_succ f parameter table lay tree leafIdx chainIdx
                  hrealizes previous hprevious]
                simp [tableInput, tablePayload, Position.children, Position.domain, position]
          have hposition : (⟨0 + steps, hstep⟩ : ChainStep) = position := by
            apply Fin.ext
            simp [position]
          change mergedCache parameter table state.ensured cache
            (tweakableHashInput parameter
              (.chain lay tree leafIdx chainIdx ⟨0 + steps, hstep⟩)
              (digestBytes (honestChain f parameter lay tree leafIdx chainIdx
                (tableOtsSecret table lay tree leafIdx chainIdx) steps))) ≠ none
          rw [hposition, hinput]
          exact mergedCache_tableInput_ne_none_of_ensured parameter table state cache
            (.chain lay tree leafIdx chainIdx position) (by trivial)
              (hensured position (by simp [position]))
        · exact CachedRun.pure _ _ _

theorem mem_runRaw_ensureCoordinate_mem
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((ensureCoordinate coordinate).run cache))) :
    coordinate ∈ finalState.ensured := by
  simp [ensureCoordinate, LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  simp [LazyRevealProbe.State.ensure]

structure EnsuresCoordinate (coordinate : Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop where
  of_run : ∀ state finalState cache finalCache fuel remaining value,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    coordinate ∈ finalState.ensured

theorem EnsuresCoordinate.done
    {coordinate : Coordinate}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hensures : EnsuresCoordinate coordinate computation)
    {state finalState : LazyRevealProbe.State Coordinate}
    {cache finalCache : SplitHashCache} {fuel remaining : Nat} {value : alpha}
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache))) :
    coordinate ∈ finalState.ensured :=
  hensures.of_run state finalState cache finalCache fuel remaining value hresult

theorem EnsuresCoordinate.bind_preserved
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : EnsuresCoordinate coordinate left) :
    EnsuresCoordinate coordinate (left >>= next) := by
  constructor
  intro state finalState cache finalCache fuel remaining value hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      have hmiddle := hleft.of_run state middleState cache middleCache fuel middleRemaining
        middleValue hraw
      exact (LazyRevealProbe.ensuredLE_of_mem_runRaw_done
        ((next middleValue).run middleCache) middleState finalState middleRemaining remaining
          (value, finalCache) hrest) hmiddle

theorem EnsuresCoordinate.bind_right
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hnext : ∀ value, EnsuresCoordinate coordinate (next value)) :
    EnsuresCoordinate coordinate (left >>= next) := by
  constructor
  intro state finalState cache finalCache fuel remaining value hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      exact (hnext middleValue).of_run middleState finalState middleCache finalCache
        middleRemaining remaining value hrest

theorem ensuresCoordinate_ensureCoordinate (coordinate : Coordinate) :
    EnsuresCoordinate coordinate (ensureCoordinate coordinate) := by
  constructor
  intro state finalState cache finalCache fuel remaining value hresult
  exact mem_runRaw_ensureCoordinate_mem coordinate state finalState cache finalCache fuel
    remaining value hresult

theorem EnsuresCoordinate.sequenceFin_component {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (index : Fin n) (hensures : EnsuresCoordinate coordinate (computation index)) :
    EnsuresCoordinate coordinate (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      rw [sequenceFin]
      cases index using Fin.cases with
      | zero => exact hensures.bind_preserved
      | succ index =>
          apply EnsuresCoordinate.bind_right
          intro head
          exact (ih (fun current : Fin n => computation current.succ) index
            hensures).bind_preserved

def EnsuresCoordinates {n : Nat} (coordinate : Fin n → Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ index, EnsuresCoordinate (coordinate index) computation

theorem ensuresCoordinates_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (coordinate : Fin n → Coordinate)
    (hcomponent : ∀ index, EnsuresCoordinate (coordinate index) (computation index)) :
    EnsuresCoordinates coordinate (sequenceFin computation) := by
  intro index
  exact EnsuresCoordinate.sequenceFin_component computation index (hcomponent index)

theorem mem_runRaw_ensureChainPrefix_mem
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) (step : ChainStep) (hstep : step.val < digit.val)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((ensureChainPrefix lay tree leafIdx chainIdx digit).run cache))) :
    Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ finalState.ensured := by
  unfold ensureChainPrefix at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hsequence, hfinish⟩ := hresult
  cases raw with
  | stopped hit => simp at hfinish
  | done sequenceState sequenceRemaining sequenceResult =>
      rcases sequenceResult with ⟨values, sequenceCache⟩
      obtain ⟨componentState, componentFinalState, componentCache, componentFinalCache,
          componentFuel, componentRemaining, componentValue, hcomponent, _, _,
          hcomponentEnsured, _⟩ :=
        sequenceFin_component_run_of_done
          (fun current : ChainStep =>
            if current.val < digit.val then
              ensureCoordinate (.position (.chain lay tree leafIdx chainIdx current))
            else pure ())
          (fun current => by
            split
            · exact (splitCachePreserving_ensureCoordinate _).ordinaryCacheIncreasing
            · exact OrdinaryCacheIncreasing.pure ())
          state sequenceState cache sequenceCache fuel sequenceRemaining values hsequence step
      rw [if_pos hstep] at hcomponent
      have hensured := hcomponentEnsured (mem_runRaw_ensureCoordinate_mem _ componentState
        componentFinalState componentCache componentFinalCache componentFuel componentRemaining
          componentValue hcomponent)
      simp [LazyRevealProbe.runRaw] at hfinish
      rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
      exact hensured

theorem ensuresCoordinate_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) (step : ChainStep) (hstep : step.val < digit.val) :
    EnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  constructor
  intro state finalState cache finalCache fuel remaining value hresult
  exact mem_runRaw_ensureChainPrefix_mem lay tree leafIdx chainIdx digit step hstep state
    finalState cache finalCache fuel remaining value hresult

set_option maxRecDepth 10000 in
theorem cachedRun_otsSignFrom_of_mem_runRaw_maskedOtsSignFrom
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (table : Coordinate → HashOutput) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) : ∀ attempts counter
      (state finalState : LazyRevealProbe.State Coordinate)
      (cache finalCache : SplitHashCache) (fuel remaining : Nat)
      (selectedCounter : Counter) (encoding : ChainIndex → Digit)
      (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache),
      StableCacheAgreesWithFn parameter finalCache f →
      (∀ position : Position, IsOtsPosition position →
        f (tableInput parameter table (.position position)) = table (.position position)) →
      LazyRevealProbe.RawResult.done finalState remaining
          (some (selectedCounter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          ((maskedOtsSignFrom parameter lay tree leafIdx message attempts counter).run cache)) →
      LazyRevealProbe.EnsuredLE finalState targetState →
      StableOrdinaryCacheLE parameter finalCache targetCache →
      CachedRun (mergedCache parameter table targetState.ensured targetCache) f
        (otsSignFrom parameter lay tree leafIdx (tableOtsSecret table lay tree leafIdx)
          message attempts counter)
  | 0, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, targetState, targetCache, hf, hrealizes, hresult,
      hensuredTarget, hcacheTarget => by
      simp [maskedOtsSignFrom, LazyRevealProbe.runRaw] at hresult
  | attempts + 1, counter, state, finalState, cache, finalCache, fuel, remaining,
      selectedCounter, encoding, targetState, targetCache, hf, hrealizes, hresult,
      hensuredTarget, hcacheTarget => by
      rw [maskedOtsSignFrom, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, hencode, hrest⟩ := hresult
      cases raw with
      | stopped hit => simp at hrest
      | done encodeState encodeRemaining encodeResult =>
          rcases encodeResult with ⟨encoded, encodeCache⟩
          simp only at hrest
          cases encoded with
          | none =>
              have hordinaryLE := ordinaryCacheIncreasing_maskedOtsSignFrom parameter lay tree
                leafIdx message attempts (counter + 1) encodeState encodeCache encodeRemaining
                  finalState remaining (some (selectedCounter, encoding)) finalCache hrest
              have hfEncode : StableCacheAgreesWithFn parameter encodeCache f :=
                fun input output hstable hcached => hf input output hstable
                  (hordinaryLE hcached)
              have hreplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
                state encodeState cache encodeCache fuel encodeRemaining none hfEncode
                  (queriesStable_encode f parameter lay tree leafIdx message
                    (BitVec.ofNat counterBits counter)) hencode
              have hencodeRun := cachedRun_mergedCache_of_stable f parameter table targetState
                targetCache _
                  (queriesStable_encode f parameter lay tree leafIdx message
                    (BitVec.ofNat counterBits counter))
                  (CachedRun.mono_stableOrdinary
                    (queriesStable_encode f parameter lay tree leafIdx message
                      (BitVec.ofNat counterBits counter))
                    ((StableOrdinaryCacheLE.of_le hordinaryLE).trans hcacheTarget) hreplay.2)
              rw [otsSignFrom]
              apply hencodeRun.bind
              rw [hreplay.1]
              exact cachedRun_otsSignFrom_of_mem_runRaw_maskedOtsSignFrom f parameter lay table tree
                leafIdx message attempts (counter + 1) encodeState finalState encodeCache
                  finalCache encodeRemaining remaining selectedCounter encoding targetState
                    targetCache hf hrealizes hrest hensuredTarget hcacheTarget
          | some selectedEncoding =>
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hrest
              obtain ⟨ensureRaw, hensure, hfinish⟩ := hrest
              cases ensureRaw with
              | stopped hit => simp at hfinish
              | done ensureState ensureRemaining ensureResult =>
                  rcases ensureResult with ⟨ensured, ensureCache⟩
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, hselected, rfl⟩
                  rcases hselected with ⟨hcounter, hencoding⟩
                  subst selectedCounter
                  subst encoding
                  have hordinaryLE := ordinaryCacheIncreasing_sequenceFin
                    (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
                      (selectedEncoding chainIdx))
                    (fun chainIdx =>
                      (splitCachePreserving_ensureChainPrefix lay tree leafIdx chainIdx
                        (selectedEncoding chainIdx)).ordinaryCacheIncreasing)
                    encodeState encodeCache encodeRemaining finalState remaining ensured
                      finalCache hensure
                  have hfEncode : StableCacheAgreesWithFn parameter encodeCache f :=
                    fun input output hstable hcached => hf input output hstable
                      (hordinaryLE hcached)
                  have hreplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                    (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter))
                    state encodeState cache encodeCache fuel encodeRemaining
                      (some selectedEncoding) hfEncode
                      (queriesStable_encode f parameter lay tree leafIdx message
                        (BitVec.ofNat counterBits counter)) hencode
                  have hencodeRun := cachedRun_mergedCache_of_stable f parameter table targetState
                    targetCache _
                      (queriesStable_encode f parameter lay tree leafIdx message
                        (BitVec.ofNat counterBits counter))
                      (CachedRun.mono_stableOrdinary
                        (queriesStable_encode f parameter lay tree leafIdx message
                          (BitVec.ofNat counterBits counter))
                        ((StableOrdinaryCacheLE.of_le hordinaryLE).trans hcacheTarget) hreplay.2)
                  have hensured : ∀ chainIdx step, step.val < (selectedEncoding chainIdx).val →
                      Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈
                        targetState.ensured := by
                    intro chainIdx step hstep
                    exact hensuredTarget ((EnsuresCoordinate.sequenceFin_component
                      (fun current : ChainIndex => ensureChainPrefix lay tree leafIdx current
                        (selectedEncoding current)) chainIdx
                      (ensuresCoordinate_ensureChainPrefix lay tree leafIdx chainIdx
                        (selectedEncoding chainIdx) step hstep)).of_run encodeState finalState
                          encodeCache finalCache encodeRemaining remaining ensured hensure)
                  have hchains : ∀ chainIdx, CachedRun
                      (mergedCache parameter table targetState.ensured targetCache) f
                      (chainWalk parameter lay tree leafIdx chainIdx 0
                        (selectedEncoding chainIdx).val
                          (tableOtsSecret table lay tree leafIdx chainIdx)) := by
                    intro chainIdx
                    exact cachedRun_chainWalk_of_ensured f parameter table targetState targetCache
                      lay tree leafIdx chainIdx hrealizes (selectedEncoding chainIdx).val
                        (fun step hstep => hensured chainIdx step hstep)
                  rw [otsSignFrom]
                  apply hencodeRun.bind
                  rw [hreplay.1]
                  apply (CachedRun.sequenceFin _ hchains).bind
                  exact CachedRun.pure _ _ _

theorem cachedRun_otsSign_of_mem_runRaw_maskedOtsSign
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (table : Coordinate → HashOutput) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (selectedCounter : Counter) (encoding : ChainIndex → Digit)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (selectedCounter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedOtsSign parameter lay tree leafIdx message).run cache))) :
    CachedRun (mergedCache parameter table finalState.ensured finalCache) f
      (otsSign parameter lay tree leafIdx (tableOtsSecret table lay tree leafIdx) message) := by
  exact cachedRun_otsSignFrom_of_mem_runRaw_maskedOtsSignFrom f parameter lay table tree leafIdx
    message encodingAttemptLimit 0 state finalState cache finalCache fuel remaining selectedCounter
      encoding finalState finalCache hf hrealizes hresult
        (LazyRevealProbe.EnsuredLE.refl finalState)
          (StableOrdinaryCacheLE.refl parameter finalCache)

theorem ensuresCoordinate_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) :
    EnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (EnsuresCoordinate.sequenceFin_component
    (fun current : ChainStep =>
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx current))) step
    (ensuresCoordinate_ensureCoordinate _)).bind_preserved

theorem ensuresCoordinates_ensureFullChains
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (step : ChainStep) :
    EnsuresCoordinates
      (fun chainIdx : ChainIndex =>
        Coordinate.position (.chain lay tree leafIdx chainIdx step))
      (sequenceFin fun chainIdx : ChainIndex =>
        ensureFullChain lay tree leafIdx chainIdx) := by
  exact ensuresCoordinates_sequenceFin
    (fun chainIdx : ChainIndex => ensureFullChain lay tree leafIdx chainIdx)
    (fun chainIdx : ChainIndex => .position (.chain lay tree leafIdx chainIdx step))
    (fun chainIdx => ensuresCoordinate_ensureFullChain lay tree leafIdx chainIdx step)

theorem ensuresCoordinate_ensureOtsLeaf_chain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    EnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (ensuresCoordinates_ensureFullChains lay tree leafIdx step chainIdx).bind_preserved

theorem ensuresCoordinate_ensureOtsLeaf_leaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    EnsuresCoordinate (.position (.leaf lay tree leafIdx))
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  apply EnsuresCoordinate.bind_right
  intro values
  exact ensuresCoordinate_ensureCoordinate _

theorem mem_runRaw_ensureFullChain_mem
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((ensureFullChain lay tree leafIdx chainIdx).run cache))) :
    Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ finalState.ensured := by
  exact (ensuresCoordinate_ensureFullChain lay tree leafIdx chainIdx step).done hresult

attribute [local irreducible] ensureFullChain ensureOtsLeaf

set_option linter.constructorNameAsVariable false in
theorem mem_runRaw_ensureOtsLeaf_mem
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((ensureOtsLeaf lay tree leafIdx).run cache))) :
    (∀ chainIdx step,
      Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ finalState.ensured) ∧
      Coordinate.position (.leaf lay tree leafIdx) ∈ finalState.ensured := by
  constructor
  · intro chainIdx step
    exact (ensuresCoordinate_ensureOtsLeaf_chain lay tree leafIdx chainIdx step).of_run
      state finalState cache finalCache fuel remaining value hresult
  · exact (ensuresCoordinate_ensureOtsLeaf_leaf lay tree leafIdx).of_run
      state finalState cache finalCache fuel remaining value hresult

theorem cachedRun_oneTimePublicKey_of_ensuredOtsLeaf
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hensured : ∀ chainIdx step,
      Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ state.ensured) :
    CachedRun (mergedCache parameter table state.ensured cache) f
      (oneTimePublicKey parameter lay tree leafIdx
        (tableOtsSecret table lay tree leafIdx)) := by
  apply CachedRun.sequenceFin
  intro chainIdx
  exact cachedRun_chainWalk_of_ensured f parameter table state cache lay tree leafIdx chainIdx
    hrealizes (chainLength - 1) (fun step _ => hensured chainIdx step)

theorem cachedRun_treeNode_zero_of_ensuredOtsLeaf
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (lay : Layer) (tree : TreeIndex) (nodeIdx : Nat)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hchains : ∀ chainIdx step,
      Coordinate.position (.chain lay tree (leafOfNat nodeIdx) chainIdx step) ∈ state.ensured)
    (hleaf : Coordinate.position (.leaf lay tree (leafOfNat nodeIdx)) ∈ state.ensured) :
    CachedRun (mergedCache parameter table state.ensured cache) f
      (treeNode parameter lay tree (tableOtsSecret table lay tree) 0 nodeIdx) := by
  rw [treeNode_zero_eq]
  have hpublic := cachedRun_oneTimePublicKey_of_ensuredOtsLeaf f parameter table state cache lay
    tree (leafOfNat nodeIdx) hrealizes hchains
  apply hpublic.bind
  have hendpoints : evalWithAnswerFn f
      (oneTimePublicKey parameter lay tree (leafOfNat nodeIdx)
        (tableOtsSecret table lay tree (leafOfNat nodeIdx))) =
      fun chainIdx => tableValue table
        (.chain lay tree (leafOfNat nodeIdx) chainIdx Position.lastChainStep) := by
    rw [eval_oneTimePublicKey]
    simpa only [honestEndpoints_def] using
      honestEndpoints_eq_table f parameter table lay tree (leafOfNat nodeIdx) hrealizes
  intro input hinput
  simp only [leafHash, queriedInputs_tweakableHash, List.mem_singleton] at hinput
  subst input
  rw [hendpoints]
  have hinput : tweakableHashInput parameter (.leaf lay tree (leafOfNat nodeIdx))
        (leafPayload fun chainIdx => tableValue table
          (.chain lay tree (leafOfNat nodeIdx) chainIdx Position.lastChainStep)) =
      tableInput parameter table (.position (.leaf lay tree (leafOfNat nodeIdx))) := by
    simp [tableInput, tablePayload, Position.children, Position.domain, leafPayload,
      Function.comp_def]
  rw [hinput]
  exact mergedCache_tableInput_ne_none_of_ensured parameter table state cache
    (.leaf lay tree (leafOfNat nodeIdx)) (by trivial) hleaf

theorem treeNode_succ_input_eq_table
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (level nodeIdx : Nat) (hlevel : level < maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
        (nodePayload
          (evalWithAnswerFn f
            (treeNode parameter lay tree (tableOtsSecret table lay tree) level (2 * nodeIdx)))
          (evalWithAnswerFn f
            (treeNode parameter lay tree (tableOtsSecret table lay tree) level
              (2 * nodeIdx + 1)))) =
      tableInput parameter table
        (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx))) := by
  have hnode : nodeIdx < 2 ^ maxLayerHeight := by
    have hpow : 0 < 2 ^ (level + 1) := pow_pos (by omega) _
    nlinarith
  have hpowTwo : 2 ≤ 2 ^ (level + 1) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ level + 1 by omega)
  have hleft : 2 * nodeIdx < 2 ^ maxLayerHeight := by nlinarith
  have hright : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := by nlinarith
  change tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
      (nodePayload
        (honestNode f parameter lay tree (tableOtsSecret table lay tree) level (2 * nodeIdx))
        (honestNode f parameter lay tree (tableOtsSecret table lay tree) level
          (2 * nodeIdx + 1))) = _
  cases level with
  | zero =>
      have hleftValue := honestNode_zero_eq_table f parameter table lay tree
        (leafOfNat (2 * nodeIdx)) hrealizes
      have hrightValue := honestNode_zero_eq_table f parameter table lay tree
        (leafOfNat (2 * nodeIdx + 1)) hrealizes
      have hleftIndex : (leafOfNat (2 * nodeIdx)).val = 2 * nodeIdx := by
        simp [leafOfNat, Nat.mod_eq_of_lt hleft]
      have hrightIndex : (leafOfNat (2 * nodeIdx + 1)).val = 2 * nodeIdx + 1 := by
        simp [leafOfNat, Nat.mod_eq_of_lt hright]
      rw [hleftIndex] at hleftValue
      rw [hrightIndex] at hrightValue
      rw [hleftValue, hrightValue]
      simp only [tableInput, tablePayload, Position.domain]
      rw [Position.children, dif_pos (by
        simpa [leafOfNat, Nat.mod_eq_of_lt hnode] using hright),
        dif_neg (show ¬0 < (⟨0, hlevel⟩ : Fin maxLayerHeight).val by simp)]
      simp [nodePayload, leafOfNat, Nat.mod_eq_of_lt hnode,
        Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]
  | succ previous =>
      have hleftSpan : 2 ^ (previous + 1) * (2 * nodeIdx + 1) ≤
          2 ^ maxLayerHeight := by
        rw [pow_succ] at hspan
        nlinarith
      have hrightSpan : 2 ^ (previous + 1) * (2 * nodeIdx + 1 + 1) ≤
          2 ^ maxLayerHeight := by
        rw [pow_succ] at hspan
        nlinarith
      rw [honestNode_eq_table_succ f parameter table lay tree hrealizes previous
          (2 * nodeIdx) (by omega) hleftSpan,
        honestNode_eq_table_succ f parameter table lay tree hrealizes previous
          (2 * nodeIdx + 1) (by omega) hrightSpan]
      simp only [tableInput, tablePayload, Position.domain]
      rw [Position.children, dif_pos (by
        simpa [leafOfNat, Nat.mod_eq_of_lt hnode] using hright),
        dif_pos (show 0 < (⟨previous + 1, hlevel⟩ : Fin maxLayerHeight).val by simp)]
      simp [nodePayload, leafOfNat, Nat.mod_eq_of_lt hnode,
        Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright]

set_option linter.unusedVariables false in
set_option linter.constructorNameAsVariable false in
theorem cachedRun_treeNode_of_mem_runRaw_ensureTreeNode
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position)) :
    ∀ level nodeIdx (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
        (state finalState targetState : LazyRevealProbe.State Coordinate)
        (cache finalCache targetCache : SplitHashCache) (fuel remaining : Nat) (value : Unit),
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
          support (LazyRevealProbe.runRaw state fuel
            ((ensureTreeNode lay tree level nodeIdx).run cache)) →
      LazyRevealProbe.EnsuredLE finalState targetState →
      CachedRun (mergedCache parameter table targetState.ensured targetCache) f
        (treeNode parameter lay tree (tableOtsSecret table lay tree) level nodeIdx)
  | 0, nodeIdx, _, state, finalState, targetState, cache, finalCache, targetCache,
      fuel, remaining, value, hresult, htarget => by
      have hensured := mem_runRaw_ensureOtsLeaf_mem lay tree (leafOfNat nodeIdx) state
        finalState cache finalCache fuel remaining value hresult
      exact cachedRun_treeNode_zero_of_ensuredOtsLeaf f parameter table targetState targetCache
        lay tree nodeIdx hrealizes (fun chainIdx step => htarget (hensured.1 chainIdx step))
          (htarget hensured.2)
  | level + 1, nodeIdx, hspan, state, finalState, targetState, cache, finalCache,
      targetCache, fuel, remaining, value, hresult, htarget => by
      have hpow : 2 ^ (level + 1) ≤ 2 ^ maxLayerHeight := calc
        2 ^ (level + 1) = 2 ^ (level + 1) * 1 := by simp
        _ ≤ 2 ^ (level + 1) * (nodeIdx + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ ≤ 2 ^ maxLayerHeight := hspan
      have hlevel : level < maxLayerHeight := by
        have := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
        omega
      rw [ensureTreeNode, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨leftRaw, hleft, hafterLeft⟩ := hresult
      cases leftRaw with
      | stopped hit => simp at hafterLeft
      | done leftState leftRemaining leftResult =>
          rcases leftResult with ⟨leftValue, leftCache⟩
          simp only at hafterLeft
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterLeft
          obtain ⟨rightRaw, hright, hlast⟩ := hafterLeft
          cases rightRaw with
          | stopped hit => simp at hlast
          | done rightState rightRemaining rightResult =>
              rcases rightResult with ⟨rightValue, rightCache⟩
              rw [dif_pos hlevel] at hlast
              have hrightTarget : LazyRevealProbe.EnsuredLE rightState targetState :=
                (LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                  ((ensureCoordinate (.position
                    (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))).run rightCache)
                  rightState finalState rightRemaining remaining (value, finalCache) hlast).trans
                    htarget
              have hleftTarget : LazyRevealProbe.EnsuredLE leftState targetState :=
                (LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                  ((ensureTreeNode lay tree level (2 * nodeIdx + 1)).run leftCache)
                  leftState rightState leftRemaining rightRemaining
                    (rightValue, rightCache) hright).trans hrightTarget
              have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤
                  2 ^ maxLayerHeight := by
                rw [pow_succ] at hspan
                nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]
              have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤
                  2 ^ maxLayerHeight := by
                rw [pow_succ] at hspan
                nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]
              have hleftRun := cachedRun_treeNode_of_mem_runRaw_ensureTreeNode f parameter
                table lay tree hrealizes level (2 * nodeIdx) hleftSpan state leftState
                  targetState cache leftCache targetCache fuel leftRemaining leftValue hleft
                    hleftTarget
              have hrightRun := cachedRun_treeNode_of_mem_runRaw_ensureTreeNode f parameter
                table lay tree hrealizes level (2 * nodeIdx + 1) hrightSpan leftState
                  rightState targetState leftCache rightCache targetCache leftRemaining
                    rightRemaining rightValue hright hrightTarget
              rw [treeNode_succ_eq]
              apply hleftRun.bind
              apply hrightRun.bind
              intro input hinput
              simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
              subst input
              rw [treeNode_succ_input_eq_table f parameter table lay tree hrealizes level
                nodeIdx hlevel hspan]
              exact mergedCache_tableInput_ne_none_of_ensured parameter table targetState
                targetCache (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)) (by trivial)
                  (htarget (mem_runRaw_ensureCoordinate_mem _ rightState finalState rightCache
                    finalCache rightRemaining remaining value hlast))

set_option maxRecDepth 10000 in
theorem cachedRun_treePath_of_mem_runRaw_ensureTreePath
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((ensureTreePath lay tree leafIdx).run cache)))
    (htarget : LazyRevealProbe.EnsuredLE finalState targetState) :
    CachedRun (mergedCache parameter table targetState.ensured targetCache) f
      (treePath parameter lay tree (tableOtsSecret table lay tree) leafIdx) := by
  unfold ensureTreePath at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨sequenceRaw, hsequence, hfinish⟩ := hresult
  cases sequenceRaw with
  | stopped hit => simp at hfinish
  | done sequenceState sequenceRemaining sequenceResult =>
      rcases sequenceResult with ⟨values, sequenceCache⟩
      simp [LazyRevealProbe.runRaw] at hfinish
      rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
      unfold treePath
      apply CachedRun.sequenceFin
      intro level
      by_cases hinLayer : level.val < layerHeight lay
      · rw [if_pos hinLayer]
        obtain ⟨componentState, componentFinalState, componentCache,
            componentFinalCache, componentFuel, componentRemaining, componentValue,
            hcomponent, _, _, hcomponentEnsured, _⟩ :=
          sequenceFin_component_run_of_done
            (fun current : Fin maxLayerHeight =>
              if current.val < layerHeight lay then
                ensureTreeNode lay tree current.val
                  (Nat.xor (leafIdx.val / 2 ^ current.val) 1)
              else pure ())
            (fun current => by
              split
              · exact (splitCachePreserving_ensureTreeNode lay tree current.val
                  (Nat.xor (leafIdx.val / 2 ^ current.val) 1)).ordinaryCacheIncreasing
              · exact OrdinaryCacheIncreasing.pure ())
            state finalState cache finalCache fuel remaining values hsequence level
        rw [if_pos hinLayer] at hcomponent
        have hspan := FtsProbeSimulation.sibling_node_bound maxLayerHeight leafIdx.val
          level.val (by omega) leafIdx.isLt
        exact cachedRun_treeNode_of_mem_runRaw_ensureTreeNode f parameter table lay tree
          hrealizes level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1) hspan
            componentState componentFinalState targetState componentCache componentFinalCache
              targetCache componentFuel componentRemaining componentValue hcomponent
                (hcomponentEnsured.trans htarget)
      · rw [if_neg hinLayer]
        exact CachedRun.pure _ _ _

theorem cachedRun_treeRoot_of_mem_runRaw_maskedTreeRoot
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (lay : Layer) (tree : TreeIndex)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (state finalState targetState : LazyRevealProbe.State Coordinate)
    (cache finalCache targetCache : SplitHashCache) (fuel remaining : Nat)
    (value : Digest)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((maskedTreeRoot lay tree).run cache)))
    (htarget : LazyRevealProbe.EnsuredLE finalState targetState) :
    CachedRun (mergedCache parameter table targetState.ensured targetCache) f
      (treeRoot parameter lay tree (tableOtsSecret table lay tree)) := by
  have hpositive : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hlevel : layerHeight lay - 1 < maxLayerHeight := by
    have hle := layerHeight_le lay
    omega
  have hlayer : layerHeight lay = layerHeight lay - 1 + 1 := by omega
  unfold maskedTreeRoot at hresult
  rw [hlayer, maskedTreeNode, dif_pos hlevel, StateT.run_bind,
    LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨ensureRaw, hensure, hreveal⟩ := hresult
  cases ensureRaw with
  | stopped hit => simp at hreveal
  | done ensureState ensureRemaining ensureResult =>
      rcases ensureResult with ⟨ensureValue, ensureCache⟩
      have hensuredTarget : LazyRevealProbe.EnsuredLE ensureState targetState :=
        (LazyRevealProbe.ensuredLE_of_mem_runRaw_done
          ((revealPosition (.node lay tree ⟨layerHeight lay - 1, hlevel⟩
            (leafOfNat 0))).run ensureCache) ensureState finalState ensureRemaining remaining
              (value, finalCache) hreveal).trans htarget
      have hspan : 2 ^ (layerHeight lay - 1 + 1) * (0 + 1) ≤
          2 ^ maxLayerHeight := by
        rw [← hlayer]
        simpa using Nat.pow_le_pow_right (n := 2) (by omega) (layerHeight_le lay)
      unfold treeRoot
      rw [hlayer]
      exact cachedRun_treeNode_of_mem_runRaw_ensureTreeNode f parameter table lay tree
        hrealizes (layerHeight lay - 1 + 1) 0 hspan state ensureState targetState cache
          ensureCache targetCache fuel ensureRemaining ensureValue hensure hensuredTarget

set_option maxRecDepth 10000 in
theorem cachedRun_signLayer_of_mem_runRaw_maskedSignLayer
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some (counter, encoding), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSignLayer parameter ftsSecret index lay).run cache)))
    (hensuredTarget : LazyRevealProbe.EnsuredLE finalState targetState)
    (hcacheTarget : StableOrdinaryCacheLE parameter finalCache targetCache) :
    CachedRun (mergedCache parameter table targetState.ensured targetCache) f
      (signLayer (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        index lay) := by
  unfold maskedSignLayer at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨messageRaw, hmessage, hafterMessage⟩ := hresult
  cases messageRaw with
  | stopped hit => simp at hafterMessage
  | done messageState messageRemaining messageResult =>
      rcases messageResult with ⟨message, messageCache⟩
      simp only at hafterMessage
      change LazyRevealProbe.RawResult.done finalState remaining
          (some (counter, encoding), finalCache) ∈ support
        (LazyRevealProbe.runRaw messageState messageRemaining
          ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache))
        at hafterMessage
      have hmessageTarget := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
        ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)
          messageState finalState messageRemaining remaining
            (some (counter, encoding), finalCache) hafterMessage
      have hmessageActual : message = evalWithAnswerFn f
          (layerMessage
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay) := by
        by_cases hbelow : lay.val + 1 < numLayers
        · let below : Layer := ⟨lay.val + 1, hbelow⟩
          have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((maskedOtsLayerAfterMessage parameter index lay message).run messageCache)
              messageState finalState messageRemaining remaining
                (some (counter, encoding), finalCache) hafterMessage
          exact maskedLayerMessage_eq_actual_of_lt
            (f := f) (parameter := parameter) (root := root) (table := table)
            (ftsSecret := ftsSecret) (index := index) (lay := lay) (below := below)
            (hbelow := hbelow) (hbelowEq := rfl) (state := state)
            (messageState := messageState) (referenceState := finalState) (cache := cache)
            (messageCache := messageCache) (fuel := fuel) (messageRemaining := messageRemaining)
            (message := message) hvaluesLE htable hrealizes hmessage
        · have hordinaryLE := ordinaryCacheIncreasing_maskedSignLayerAfterMessage parameter
            index lay message messageState messageCache messageRemaining finalState remaining
              (some (counter, encoding)) finalCache hafterMessage
          have hfMessage : StableCacheAgreesWithFn parameter messageCache f :=
            fun input output hstable hcached => hf input output hstable (hordinaryLE hcached)
          exact maskedLayerMessage_eq_actual_of_not_lt f parameter root table ftsSecret index lay
            hbelow state messageState cache messageCache fuel messageRemaining message hfMessage
              hmessage
      have hmessageRun : CachedRun
          (mergedCache parameter table targetState.ensured targetCache) f
          (layerMessage
            (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) index lay) := by
        by_cases hbelow : lay.val + 1 < numLayers
        · let below : Layer := ⟨lay.val + 1, hbelow⟩
          rw [layerMessage, dif_pos hbelow]
          have hmessage' := hmessage
          rw [maskedLayerMessage, dif_pos hbelow] at hmessage'
          exact cachedRun_treeRoot_of_mem_runRaw_maskedTreeRoot f parameter table below
            (treeIndexAt index below) hrealizes state messageState targetState cache messageCache
              targetCache fuel messageRemaining message hmessage'
                (hmessageTarget.trans hensuredTarget)
        · rw [layerMessage, dif_neg hbelow]
          have hmessage' := hmessage
          rw [maskedLayerMessage, dif_neg hbelow] at hmessage'
          have hordinaryLE := ordinaryCacheIncreasing_maskedSignLayerAfterMessage parameter
            index lay message messageState messageCache messageRemaining finalState remaining
              (some (counter, encoding)) finalCache hafterMessage
          have hfMessage : StableCacheAgreesWithFn parameter messageCache f :=
            fun input output hstable hcached => hf input output hstable (hordinaryLE hcached)
          have hreplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
            (ftsKey parameter index (ftsSecret index)) state messageState cache messageCache fuel
              messageRemaining message hfMessage
                (queriesStable_ftsKey f parameter index (ftsSecret index)) hmessage'
          exact cachedRun_mergedCache_of_stable f parameter table targetState targetCache _
            (queriesStable_ftsKey f parameter index (ftsSecret index))
              (CachedRun.mono_stableOrdinary
                (queriesStable_ftsKey f parameter index (ftsSecret index))
                ((StableOrdinaryCacheLE.of_le hordinaryLE).trans hcacheTarget) hreplay.2)
      unfold maskedOtsLayerAfterMessage at hafterMessage
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterMessage
      obtain ⟨otsRaw, hots, hafterOts⟩ := hafterMessage
      cases otsRaw with
      | stopped hit => simp at hafterOts
      | done otsState otsRemaining otsResult =>
          rcases otsResult with ⟨part, otsCache⟩
          cases part with
          | none => simp [LazyRevealProbe.runRaw] at hafterOts
          | some selectedPart =>
              rcases selectedPart with ⟨selectedCounter, selectedEncoding⟩
              simp only at hafterOts
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hafterOts
              obtain ⟨pathRaw, hpath, hfinish⟩ := hafterOts
              cases pathRaw with
              | stopped hit => simp at hfinish
              | done pathState pathRemaining pathResult =>
                  rcases pathResult with ⟨pathValue, pathCache⟩
                  have hpathCache := splitCachePreserving_ensureTreePath lay
                    (treeIndexAt index lay) (leafIndexAt index lay) otsState otsCache
                      otsRemaining pathState pathRemaining pathValue pathCache hpath
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, hpart, rfl⟩
                  rcases hpart with ⟨hcounter, hencoding⟩
                  subst selectedCounter
                  subst selectedEncoding
                  have hfOts := hf
                  rw [hpathCache] at hfOts
                  have hpathEnsured := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                    ((ensureTreePath lay (treeIndexAt index lay)
                      (leafIndexAt index lay)).run otsCache) otsState finalState otsRemaining
                        remaining (pathValue, finalCache) hpath
                  have hotsCacheTarget : StableOrdinaryCacheLE parameter otsCache
                      targetCache := by
                    have hotsToFinal : ordinaryQueryCache otsCache ≤
                        ordinaryQueryCache finalCache := by rw [hpathCache]
                    exact (StableOrdinaryCacheLE.of_le hotsToFinal).trans hcacheTarget
                  have hotsRun :=
                    cachedRun_otsSignFrom_of_mem_runRaw_maskedOtsSignFrom f parameter lay table
                      (treeIndexAt index lay) (leafIndexAt index lay) message encodingAttemptLimit
                        0 messageState otsState messageCache otsCache messageRemaining otsRemaining
                          counter encoding targetState targetCache hfOts hrealizes hots
                            (hpathEnsured.trans hensuredTarget) hotsCacheTarget
                  have hotsEval := maskedOtsSign_some_honest_eval f parameter lay
                    (treeIndexAt index lay) (leafIndexAt index lay)
                      (tableOtsSecret table lay (treeIndexAt index lay) (leafIndexAt index lay))
                        message messageState otsState messageCache otsCache messageRemaining
                          otsRemaining counter encoding hfOts hots
                  have hpathRun := cachedRun_treePath_of_mem_runRaw_ensureTreePath f parameter table
                    lay (treeIndexAt index lay) (leafIndexAt index lay) hrealizes otsState
                      finalState otsCache finalCache otsRemaining remaining pathValue targetState
                        targetCache hpath hensuredTarget
                  unfold signLayer
                  apply hmessageRun.bind
                  rw [← hmessageActual]
                  apply hotsRun.bind
                  unfold otsSign at hotsEval
                  rw [hotsEval]
                  apply hpathRun.bind
                  exact CachedRun.pure _ _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem successfulSignRun_of_mem_runRaw_maskedSignAfterDigest
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : Message) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) (signature : Signature)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hdigest : SuccessfulDigestRun f
      (mergedCache parameter table targetState.ensured targetCache)
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        message randomness index leaves)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some signature, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSignAfterDigest parameter ftsSecret randomness index leaves).run cache)))
    (hensuredTarget : LazyRevealProbe.EnsuredLE finalState targetState)
    (hcacheTarget : StableOrdinaryCacheLE parameter finalCache targetCache) :
    SuccessfulSignRun f (mergedCache parameter table targetState.ensured targetCache)
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        message signature := by
  unfold maskedSignAfterDigest at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨pathRaw, hpath, hafterPath⟩ := hresult
  cases pathRaw with
  | stopped hit => simp at hafterPath
  | done pathState pathRemaining pathResult =>
      rcases pathResult with ⟨ftsPath, pathCache⟩
      simp only at hafterPath
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterPath
      obtain ⟨layersRaw, hlayers, hafterLayers⟩ := hafterPath
      cases layersRaw with
      | stopped hit => simp at hafterLayers
      | done layersState layersRemaining layersResult =>
          rcases layersResult with ⟨layers, layersCache⟩
          rw [← maskedSignLayers_eq_sequenceFin parameter ftsSecret index] at hlayers
          have hlayersLE := ordinaryCacheIncreasing_maskedSignLayers parameter ftsSecret index
            pathState pathCache pathRemaining layersState layersRemaining layers layersCache hlayers
          simp only at hafterLayers
          cases hparts : traverseOption layers with
          | none =>
              simp [hparts, LazyRevealProbe.runRaw] at hafterLayers
          | some parts =>
              rw [hparts, StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hafterLayers
              obtain ⟨revealedRaw, hrevealed, hfinish⟩ := hafterLayers
              cases revealedRaw with
              | stopped hit => simp at hfinish
              | done revealedState revealedRemaining revealedResult =>
                  rcases revealedResult with ⟨revealed, revealedCache⟩
                  have hrevealedLE := ordinaryCacheIncreasing_sequenceFin
                    (fun lay => revealLayerValues index lay (parts lay).2)
                    (fun lay => ordinaryCacheIncreasing_revealLayerValues index lay (parts lay).2)
                    layersState layersCache layersRemaining revealedState revealedRemaining
                      revealed revealedCache hrevealed
                  have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                    ((sequenceFin fun lay => revealLayerValues index lay (parts lay).2).run
                      layersCache) layersState revealedState layersRemaining revealedRemaining
                        (revealed, revealedCache) hrevealed
                  have hensuredLE := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                    ((sequenceFin fun lay => revealLayerValues index lay (parts lay).2).run
                      layersCache) layersState revealedState layersRemaining revealedRemaining
                        (revealed, revealedCache) hrevealed
                  simp [LazyRevealProbe.runRaw] at hfinish
                  rcases hfinish with ⟨rfl, rfl, hsignature, rfl⟩
                  have hfPath : StableCacheAgreesWithFn parameter pathCache f :=
                    fun input output hstable hcached => hf input output hstable
                      (hrevealedLE (hlayersLE hcached))
                  have hftsReplay := replay_of_mem_runRaw_ordinaryHashImpl_of_stable f parameter
                    (ftsOpen parameter index leaves (ftsSecret index)) state pathState cache
                      pathCache fuel pathRemaining ftsPath hfPath
                        (queriesStable_ftsOpen f parameter index leaves (ftsSecret index)) hpath
                  have hftsRun := cachedRun_mergedCache_of_stable f parameter table targetState
                    targetCache _ (queriesStable_ftsOpen f parameter index leaves (ftsSecret index))
                      (CachedRun.mono_stableOrdinary
                        (queriesStable_ftsOpen f parameter index leaves (ftsSecret index))
                        ((StableOrdinaryCacheLE.of_le (hlayersLE.trans hrevealedLE)).trans
                          hcacheTarget) hftsReplay.2)
                  rw [hsignature]
                  refine ⟨index, leaves,
                    (fun lay => ((parts lay).1, (revealed lay).1, (revealed lay).2)),
                    hdigest, rfl, hftsReplay.1.symm, rfl, rfl, rfl, hftsRun, ?_, ?_⟩
                  · intro lay
                    obtain ⟨componentState, componentFinalState, componentCache,
                        componentFinalCache, componentFuel, componentRemaining, part, hcomponent,
                        hselected, hcomponentValuesLE, hcomponentEnsuredLE,
                        hcomponentCacheLE⟩ :=
                      maskedSignLayers_component_run parameter ftsSecret index pathState
                        layersState pathCache layersCache pathRemaining layersRemaining layers
                          hlayers lay
                    have hpartsAt := traverseOption_eq_some_apply layers parts hparts lay
                    have hpart : part = some (parts lay) := hselected.symm.trans hpartsAt
                    rw [hpart, maskedSignLayerAt_eq] at hcomponent
                    obtain ⟨revealState, revealFinalState, revealCache, revealFinalCache,
                        revealFuel, revealRemaining, revealValue, hrevealComponent,
                        hrevealSelected, hrevealValuesLE, _, _⟩ :=
                      sequenceFin_component_run_of_done
                        (fun otherLay => revealLayerValues index otherLay (parts otherLay).2)
                        (fun otherLay => ordinaryCacheIncreasing_revealLayerValues index otherLay
                          (parts otherLay).2) layersState finalState layersCache finalCache
                            layersRemaining remaining revealed hrevealed lay
                    have hfComponent : StableCacheAgreesWithFn parameter componentFinalCache f :=
                      fun input output hstable hcached => hf input output hstable
                        (hrevealedLE (hcomponentCacheLE hcached))
                    have htableComponent : ∀ coordinate output,
                        componentFinalState.values coordinate = some output →
                          output = table coordinate :=
                      fun coordinate output hvalue => htable coordinate output
                        (hvaluesLE coordinate output
                          (hcomponentValuesLE coordinate output hvalue))
                    have htableReveal : ∀ coordinate output,
                        revealFinalState.values coordinate = some output →
                          output = table coordinate :=
                      fun coordinate output hvalue => htable coordinate output
                        (hrevealValuesLE coordinate output hvalue)
                    change evalWithAnswerFn f
                      (signLayer
                        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
                          index lay) =
                        some ((parts lay).1, (revealed lay).1, (revealed lay).2)
                    rw [hrevealSelected]
                    exact maskedSignLayer_and_reveal_eval f parameter root table ftsSecret index lay
                      (parts lay).1 (parts lay).2 componentState componentFinalState componentCache
                        componentFinalCache componentFuel componentRemaining revealState
                          revealFinalState revealCache revealFinalCache revealFuel revealRemaining
                            revealValue hfComponent htableComponent htableReveal hrealizes hcomponent
                              hrevealComponent
                  · intro lay
                    obtain ⟨componentState, componentFinalState, componentCache,
                        componentFinalCache, componentFuel, componentRemaining, part, hcomponent,
                        hselected, hcomponentValuesLE, hcomponentEnsuredLE,
                        hcomponentCacheLE⟩ :=
                      maskedSignLayers_component_run parameter ftsSecret index pathState
                        layersState pathCache layersCache pathRemaining layersRemaining layers
                          hlayers lay
                    have hpartsAt := traverseOption_eq_some_apply layers parts hparts lay
                    have hpart : part = some (parts lay) := hselected.symm.trans hpartsAt
                    rw [hpart, maskedSignLayerAt_eq] at hcomponent
                    have hfComponent : StableCacheAgreesWithFn parameter componentFinalCache f :=
                      fun input output hstable hcached => hf input output hstable
                        (hrevealedLE (hcomponentCacheLE hcached))
                    have htableComponent : ∀ coordinate output,
                        componentFinalState.values coordinate = some output →
                          output = table coordinate :=
                      fun coordinate output hvalue => htable coordinate output
                        (hvaluesLE coordinate output (hcomponentValuesLE coordinate output hvalue))
                    exact cachedRun_signLayer_of_mem_runRaw_maskedSignLayer f parameter root table
                      ftsSecret index lay componentState componentFinalState componentCache
                        componentFinalCache componentFuel componentRemaining (parts lay).1
                          (parts lay).2 targetState targetCache hfComponent htableComponent hrealizes
                            hcomponent ((hcomponentEnsuredLE.trans hensuredLE).trans
                              hensuredTarget)
                              ((StableOrdinaryCacheLE.of_le
                                (hcomponentCacheLE.trans hrevealedLE)).trans hcacheTarget)

set_option maxRecDepth 10000 in
theorem successfulSignRun_of_mem_runRaw_maskedSign
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (message : Message) (signature : Signature)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (some signature, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSign parameter root ftsSecret message).run cache)))
    (hensuredTarget : LazyRevealProbe.EnsuredLE finalState targetState)
    (hcacheTarget : StableOrdinaryCacheLE parameter finalCache targetCache) :
    SuccessfulSignRun f (mergedCache parameter table targetState.ensured targetCache)
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
        message signature := by
  let secretKey : SecretKey :=
    ⟨parameter, root, tableOtsSecret table, ftsSecret⟩
  let digestSecretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  unfold maskedSign at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨loopRaw, hloop, hrest⟩ := hresult
  cases loopRaw with
  | stopped hit => simp at hrest
  | done loopState loopRemaining loopResult =>
      rcases loopResult with ⟨selected, loopCache⟩
      simp only at hrest
      cases selected with
      | none => simp [LazyRevealProbe.runRaw] at hrest
      | some selected =>
          obtain ⟨randomness, index, leaves⟩ := selected
          have hcacheLE := ordinaryCacheIncreasing_maskedSignAfterDigest parameter ftsSecret
            randomness index leaves loopState loopCache loopRemaining finalState remaining
              (some signature) finalCache hrest
          have hdigestLoop := successfulDigestLoop_of_mem_runRaw_ordinaryRomImpl f
            digestSecretKey message digestAttemptLimit randomness index leaves state loopState
              cache loopCache fuel loopRemaining finalCache hcacheLE hf hloop
          have hdigest : SuccessfulDigestRun f (ordinaryQueryCache finalCache) secretKey message
              randomness index leaves := by
            simpa only [SuccessfulDigestRun, signAttempt, digestSecretKey, secretKey] using
              hdigestLoop
          have hdigestMerged : SuccessfulDigestRun f
              (mergedCache parameter table targetState.ensured targetCache) secretKey message
                randomness index leaves :=
            ⟨hdigest.1, hdigest.2.1,
              cachedRun_mergedCache_of_stable f parameter table targetState targetCache _
                (queriesStable_signAttempt f secretKey message randomness)
                  (CachedRun.mono_stableOrdinary
                    (queriesStable_signAttempt f secretKey message randomness) hcacheTarget
                      hdigest.2.2)⟩
          exact successfulSignRun_of_mem_runRaw_maskedSignAfterDigest f parameter root table
            ftsSecret message randomness index leaves signature loopState finalState loopCache
              finalCache loopRemaining remaining targetState targetCache hf htable hrealizes (by
                simpa only [secretKey] using hdigestMerged) hrest hensuredTarget hcacheTarget

set_option maxRecDepth 10000 in
theorem successfulSignRuns_signingTraceComputation
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (root : Digest)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (value : alpha) (signingLog : QueryLog SigningSpec)
    (targetState : LazyRevealProbe.State Coordinate) (targetCache : SplitHashCache)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        ((value, signingLog), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (signingTraceComputation computation)).run cache)))
    (hensuredTarget : LazyRevealProbe.EnsuredLE finalState targetState)
    (hcacheTarget : StableOrdinaryCacheLE parameter finalCache targetCache) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f (mergedCache parameter table targetState.ensured targetCache)
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature := by
  induction computation using OracleComp.inductionOn generalizing signingLog state cache fuel with
  | pure result =>
      simp [signingTraceComputation, LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, hvalue, rfl⟩
      rcases hvalue with ⟨rfl, rfl⟩
      intro entry signature hentry
      simp at hentry
  | query_bind input next ih =>
      rw [signingTraceComputation_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨queryRaw, hquery, hrest⟩ := hresult
      cases queryRaw with
      | stopped hit => simp at hrest
      | done queryState queryRemaining queryResult =>
          rcases queryResult with ⟨output, queryCache⟩
          simp only at hrest
          rw [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind,
            LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailRaw, htail, hfinish⟩ := hrest
          cases tailRaw with
          | stopped hit => simp at hfinish
          | done tailState tailRemaining tailResult =>
              rcases tailResult with ⟨⟨tailValue, tailLog⟩, tailCache⟩
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨rfl, rfl, houtputs, rfl⟩
              rcases houtputs with ⟨rfl, rfl⟩
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
                  (signingTraceComputation (next output))).run queryCache)
                    queryState finalState queryRemaining remaining
                      ((value, tailLog), finalCache) htail
              have hensuredLE := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
                  (signingTraceComputation (next output))).run queryCache)
                    queryState finalState queryRemaining remaining
                      ((value, tailLog), finalCache) htail
              have hstableCacheLE : StableOrdinaryCacheLE parameter queryCache finalCache := by
                intro stableInput cached hstable hcached
                exact ((ordinaryEntryPreservingImpl_maskedExpandedAdversaryImpl parameter root
                  ftsSecret stableInput hstable).simulateQ
                    (signingTraceComputation (next output))) queryState queryCache queryRemaining
                      finalState remaining (value, tailLog) finalCache cached hcached htail
              have htableQuery : ∀ coordinate cached,
                  queryState.values coordinate = some cached → cached = table coordinate :=
                fun coordinate cached hcached =>
                  htable coordinate cached (hvaluesLE coordinate cached hcached)
              have hfQuery : StableCacheAgreesWithFn parameter queryCache f :=
                StableCacheAgreesWithFn.of_run
                  (fun stableInput hstable =>
                    (ordinaryEntryPreservingImpl_maskedExpandedAdversaryImpl parameter root
                      ftsSecret stableInput hstable).simulateQ
                        (signingTraceComputation (next output)))
                  queryState finalState queryCache finalCache queryRemaining remaining
                    (value, tailLog) hf htail
              intro entry signature hentry hsignature
              simp only [List.mem_append] at hentry
              rcases hentry with hfragment | htailEntry
              · cases input with
                | inl oracleQuery => simp [signingLogFragment] at hfragment
                | inr message =>
                    have hentryEq : entry = ⟨message, output⟩ := by
                      simpa [signingLogFragment] using hfragment
                    subst entry
                    change LazyRevealProbe.RawResult.done queryState queryRemaining
                        (output, queryCache) ∈ support
                      (LazyRevealProbe.runRaw state fuel
                        ((maskedSign parameter root ftsSecret message).run cache)) at hquery
                    change output = some signature at hsignature
                    subst output
                    exact successfulSignRun_of_mem_runRaw_maskedSign f parameter root table
                      ftsSecret message signature state queryState cache queryCache fuel
                        queryRemaining targetState targetCache hfQuery htableQuery hrealizes hquery
                          (hensuredLE.trans hensuredTarget)
                            (hstableCacheLE.trans hcacheTarget)
              · exact ih output queryState queryCache queryRemaining tailLog htail entry signature
                  htailEntry hsignature

set_option maxRecDepth 10000 in
theorem successfulSignRuns_retainedGameRestComputation
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (forgery : Forgery) (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (((forgery, signingLog), verified), finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (retainedGameRestComputation adversary ⟨root, parameter⟩)).run cache))) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f (mergedCache parameter table finalState.ensured finalCache)
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature := by
  rw [simulateQ_maskedExpanded_retainedGameRestComputation, StateT.run_bind,
    LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨prefixRaw, hprefix, hrest⟩ := hresult
  cases prefixRaw with
  | stopped hit => simp at hrest
  | done prefixState prefixRemaining prefixResult =>
      rcases prefixResult with ⟨⟨prefixForgery, prefixLog⟩, prefixCache⟩
      simp only at hrest
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
      obtain ⟨verifyRaw, hverify, hfinish⟩ := hrest
      cases verifyRaw with
      | stopped hit => simp at hfinish
      | done verifyState verifyRemaining verifyResult =>
          rcases verifyResult with ⟨prefixVerified, verifyCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, houtputs, rfl⟩
          rcases houtputs with ⟨hprefixOutput, rfl⟩
          rcases hprefixOutput with ⟨rfl, rfl⟩
          have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((simulateQ (probingRomImpl parameter)
              (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
                prefixCache) prefixState finalState prefixRemaining remaining
                  (verified, finalCache) hverify
          have hensuredLE := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
            ((simulateQ (probingRomImpl parameter)
              (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
                prefixCache) prefixState finalState prefixRemaining remaining
                  (verified, finalCache) hverify
          have hstableCacheLE : StableOrdinaryCacheLE parameter prefixCache finalCache := by
            intro input output hstable hcached
            exact ((ordinaryEntryPreservingImpl_probingRomImpl parameter input hstable).simulateQ
              (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)) prefixState
                prefixCache prefixRemaining finalState remaining verified finalCache output hcached
                  hverify
          have htablePrefix : ∀ coordinate output,
              prefixState.values coordinate = some output → output = table coordinate :=
            fun coordinate output hcached =>
              htable coordinate output (hvaluesLE coordinate output hcached)
          have hfPrefix : StableCacheAgreesWithFn parameter prefixCache f :=
            StableCacheAgreesWithFn.of_run
              (fun input hstable =>
                (ordinaryEntryPreservingImpl_probingRomImpl parameter input hstable).simulateQ
                  (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature))
              prefixState finalState prefixCache finalCache prefixRemaining remaining verified hf
                hverify
          exact successfulSignRuns_signingTraceComputation f parameter root table ftsSecret
            (adversary.main ⟨root, parameter⟩) state prefixState cache prefixCache fuel
              prefixRemaining forgery signingLog finalState finalCache hfPrefix htablePrefix
                hrealizes hprefix hensuredLE hstableCacheLE

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem successfulSignRuns_maskedRetainedGameAfterFtsSecrets
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel remaining : Nat) (finalState : LazyRevealProbe.State Coordinate)
    (finalCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        ((root, ((forgery, signingLog), verified)), finalCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache))) :
    ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ signingLog → entry.2 = some signature →
        SuccessfulSignRun f (mergedCache parameter table finalState.ensured finalCache)
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
            entry.1 signature := by
  unfold maskedRetainedGameAfterFtsSecrets at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨rootRaw, hroot, hafterRoot⟩ := hresult
  cases rootRaw with
  | stopped hit => simp at hafterRoot
  | done rootState rootRemaining rootResult =>
      rcases rootResult with ⟨sampledRoot, rootCache⟩
      simp only at hafterRoot
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterRoot
      obtain ⟨publishRaw, hpublish, hafterPublish⟩ := hafterRoot
      cases publishRaw with
      | stopped hit => simp at hafterPublish
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          simp only at hafterPublish
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterPublish
          obtain ⟨restRaw, hrest, hfinish⟩ := hafterPublish
          cases restRaw with
          | stopped hit => simp at hfinish
          | done restState restRemaining restResult =>
              rcases restResult with ⟨⟨prefixForgery, prefixLog⟩, restCache⟩
              simp only at hfinish
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hfinish
              obtain ⟨verifyRaw, hverify, hreturn⟩ := hfinish
              cases verifyRaw with
              | stopped hit => simp at hreturn
              | done verifyState verifyRemaining verifyResult =>
                rcases verifyResult with ⟨prefixVerified, verifyCache⟩
                simp [LazyRevealProbe.runRaw] at hreturn
                rcases hreturn with ⟨rfl, rfl, houtput, rfl⟩
                rcases houtput with ⟨hrootEq, hrestEq, rfl⟩
                rcases hrestEq with ⟨rfl, rfl⟩
                have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                  ((simulateQ (verifierRomImpl parameter)
                    (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                      forgery.signature)).run restCache)
                    restState finalState restRemaining remaining (verified, finalCache) hverify
                have hensuredLE := LazyRevealProbe.ensuredLE_of_mem_runRaw_done
                  ((simulateQ (verifierRomImpl parameter)
                    (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                      forgery.signature)).run restCache)
                    restState finalState restRemaining remaining (verified, finalCache) hverify
                have hstableCacheLE : StableOrdinaryCacheLE parameter restCache finalCache := by
                  intro input output _ hcached
                  exact (ordinaryEntryPreservingImpl_verifierRomImpl parameter input).simulateQ
                    (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                      forgery.signature) restState restCache restRemaining finalState remaining
                        verified finalCache output hcached hverify
                have htableRest : ∀ coordinate output,
                    restState.values coordinate = some output → output = table coordinate :=
                  fun coordinate output hcached =>
                    htable coordinate output (hvaluesLE coordinate output hcached)
                have hfRest : StableCacheAgreesWithFn parameter restCache f :=
                  StableCacheAgreesWithFn.of_run
                    (fun input _ =>
                      (ordinaryEntryPreservingImpl_verifierRomImpl parameter input).simulateQ
                        (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                          forgery.signature))
                    restState finalState restCache finalCache restRemaining remaining verified hf
                      hverify
                have hruns := successfulSignRuns_signingTraceComputation f parameter sampledRoot
                  table ftsSecret (adversary.main ⟨sampledRoot, parameter⟩) publishState restState
                    publishCache restCache publishRemaining restRemaining forgery signingLog
                      finalState finalCache hfRest htableRest hrealizes hrest hensuredLE
                        hstableCacheLE
                simpa only [hrootEq] using hruns

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem chainInvariant_maskedRetainedGameAfterFtsSecrets_mergedCache
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel remaining : Nat) (finalState : LazyRevealProbe.State Coordinate)
    (finalCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hf : StableCacheAgreesWithFn parameter finalCache f)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        ((root, ((forgery, signingLog), verified)), finalCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache))) :
    ∃ verifierState verifierFuel verifierCache,
      ChainInvariant parameter
        (CoveredChainCoordinate f
          (mergedCache parameter table finalState.ensured finalCache)
          (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
        verifierState verifierCache ∧
      LazyRevealProbe.RawResult.done finalState remaining (verified, finalCache) ∈ support
        (LazyRevealProbe.runRaw verifierState verifierFuel
          ((simulateQ (verifierRomImpl parameter)
            (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
              verifierCache)) := by
  exact chainInvariant_maskedRetainedGameAfterFtsSecrets adversary f parameter table ftsSecret
    (mergedCache parameter table finalState.ensured finalCache) fuel remaining finalState
      finalCache root forgery signingLog verified
        (successfulSignRuns_maskedRetainedGameAfterFtsSecrets adversary f parameter table
          ftsSecret fuel remaining finalState finalCache root forgery signingLog verified hf
            htable hrealizes hresult) hf htable hrealizes hresult

theorem revealPositionValues_makes_values
    (table : Coordinate → HashOutput) (positions : List Position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (values : List Digest)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (values, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealPositionValues positions).run cache))) :
    ∀ position, position ∈ positions →
      finalState.values (.position position) = some (table (.position position)) := by
  induction positions generalizing state cache fuel values with
  | nil => simp
  | cons position positions ih =>
      rw [revealPositionValues, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨headRaw, hhead, hrest⟩ := hresult
      cases headRaw with
      | stopped hit => simp at hrest
      | done headState headRemaining headResult =>
          rcases headResult with ⟨headValue, headCache⟩
          simp only at hrest
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailRaw, htail, hfinish⟩ := hrest
          cases tailRaw with
          | stopped hit => simp at hfinish
          | done tailState tailRemaining tailResult =>
              rcases tailResult with ⟨tailValues, tailCache⟩
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                ((revealPositionValues positions).run headCache)
                  headState tailState headRemaining tailRemaining (tailValues, tailCache) htail
              simp [LazyRevealProbe.runRaw] at hfinish
              rcases hfinish with ⟨hstate, hfuel, hvalues, hcache⟩
              subst finalState
              subst remaining
              subst values
              subst finalCache
              intro other hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with heq | hmem
              · subst other
                obtain ⟨output, _, hvalue⟩ := mem_runRaw_revealCoordinate_value
                  (.position position) state headState cache headCache fuel headRemaining headValue
                    (by simpa [revealPosition] using hhead)
                rw [hvaluesLE _ _ hvalue, htable _ output (hvaluesLE _ _ hvalue)]
              · exact ih headState headCache headRemaining tailValues htail other hmem

theorem revealTableInputChildren_makes_available
    (table : Coordinate → HashOutput) (position : Position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (htable : ∀ coordinate output, finalState.values coordinate = some output →
      output = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((revealTableInputChildren (.position position)).run cache))) :
    TableInputAvailable table finalState (.position position) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      by_cases hzero : step.val = 0
      · simp only [revealTableInputChildren, hzero, ↓reduceIte] at hresult
        rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
        obtain ⟨raw, hreveal, hfinish⟩ := hresult
        cases raw with
        | stopped hit => simp at hfinish
        | done revealState revealRemaining revealResult =>
            rcases revealResult with ⟨revealed, revealCache⟩
            simp [LazyRevealProbe.runRaw] at hfinish
            rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨output, _, hvalue⟩ := mem_runRaw_revealCoordinate_value
              (.chainStart lay tree leafIdx chainIdx) state finalState cache finalCache fuel
                remaining revealed (by simpa [revealChainStart] using hreveal)
            simp only [TableInputAvailable, hzero, ↓reduceIte]
            rw [hvalue, htable _ output hvalue]
      · simp only [revealTableInputChildren, hzero, ↓reduceIte] at hresult
        rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
        obtain ⟨raw, hvalues, hfinish⟩ := hresult
        cases raw with
        | stopped hit => simp at hfinish
        | done valuesState valuesRemaining valuesResult =>
            rcases valuesResult with ⟨values, valuesCache⟩
            simp [LazyRevealProbe.runRaw] at hfinish
            rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
            simpa only [TableInputAvailable, hzero, ↓reduceIte] using
              revealPositionValues_makes_values table
                (Position.chain lay tree leafIdx chainIdx step).children state finalState cache
                  finalCache fuel remaining values htable hvalues
  | leaf lay tree leafIdx =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues
  | node lay tree level nodeIdx =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues
  | ftsLeaf index tree leafIdx =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues
  | ftsNode index tree level nodeIdx =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues
  | ftsRoots index =>
      simp only [revealTableInputChildren] at hresult
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
      obtain ⟨raw, hvalues, hfinish⟩ := hresult
      cases raw with
      | stopped hit => simp at hfinish
      | done valuesState valuesRemaining valuesResult =>
          rcases valuesResult with ⟨values, valuesCache⟩
          simp [LazyRevealProbe.runRaw] at hfinish
          rcases hfinish with ⟨rfl, rfl, rfl, rfl⟩
          exact revealPositionValues_makes_values table _ state finalState cache finalCache fuel
            remaining values htable hvalues

theorem resolveKnownInput_returns_table_of_available
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (havailable : TableInputAvailable table state coordinate)
    (htable : ∀ other cached, finalState.values other = some cached →
      cached = table other)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveKnownInput parameter coordinate
          (tableInput parameter table coordinate)).run cache))) :
    output = table coordinate ∧
      finalCache (.ordinary (tableInput parameter table coordinate)) = some output := by
  have hcached := returnsCachedOrdinary_resolveKnownInput parameter coordinate
    (tableInput parameter table coordinate) state cache fuel finalState remaining output
      finalCache hresult
  unfold resolveKnownInput at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
    runRaw_peekTableInput_of_available parameter table state cache fuel coordinate havailable]
    at hresult
  simp only [pure_bind, ↓reduceIte] at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hrest⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hrevealed := mem_runRaw_revealCoordinateOutput_value coordinate state revealState
        cache revealCache fuel revealRemaining revealed hreveal
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        (((publishCoordinate coordinate >>= fun _ => do
          modify fun workingCache : SplitHashCache =>
            Function.update workingCache
              (.ordinary (tableInput parameter table coordinate)) (some revealed)
          pure revealed).run revealCache))
        revealState finalState revealRemaining remaining (output, finalCache) hrest
      have hfinalValue := hvaluesLE coordinate revealed hrevealed.1
      have hrevealedTable := htable coordinate revealed hfinalValue
      have houtput : output = revealed := by
        simp [publishCoordinate, LazyRevealProbe.publishQuery,
          StateT.run_modify, LazyRevealProbe.runRaw] at hrest
        exact congrArg Prod.fst (LazyRevealProbe.RawResult.done.inj hrest).2.2
      exact ⟨houtput.trans hrevealedTable, hcached⟩

theorem resolveVerifierInput_returns_table_of_uncached
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (huncached : cache (.ordinary
      (tableInput parameter table (.position position))) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveVerifierInput parameter (.position position)
          (tableInput parameter table (.position position))).run cache))) :
    output = table (.position position) ∧
      finalCache (.ordinary (tableInput parameter table (.position position))) = some output := by
  unfold resolveVerifierInput at hresult
  simp [StateT.run_get, huncached] at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hresolve⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hresolve
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((resolveKnownInput parameter (.position position)
          (tableInput parameter table (.position position))).run revealCache)
          revealState finalState revealRemaining remaining (output, finalCache) hresolve
      have htableReveal : ∀ coordinate cached,
          revealState.values coordinate = some cached → cached = table coordinate :=
        fun coordinate cached hcached =>
          htable coordinate cached (hvaluesLE coordinate cached hcached)
      have havailable := revealTableInputChildren_makes_available table position state revealState
        cache revealCache fuel revealRemaining revealed htableReveal hreveal
      exact resolveKnownInput_returns_table_of_available parameter table (.position position)
        revealState finalState revealCache finalCache revealRemaining remaining output havailable
          htable hresolve

theorem resolveVerifierInput_makes_available_of_uncached
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (huncached : cache (.ordinary
      (tableInput parameter table (.position position))) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveVerifierInput parameter (.position position)
          (tableInput parameter table (.position position))).run cache))) :
    TableInputAvailable table finalState (.position position) := by
  unfold resolveVerifierInput at hresult
  simp [StateT.run_get, huncached] at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hresolve⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hresolve
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((resolveKnownInput parameter (.position position)
          (tableInput parameter table (.position position))).run revealCache)
          revealState finalState revealRemaining remaining (output, finalCache) hresolve
      have htableReveal : ∀ coordinate cached,
          revealState.values coordinate = some cached → cached = table coordinate :=
        fun coordinate cached hcached =>
          htable coordinate cached (hvaluesLE coordinate cached hcached)
      exact (revealTableInputChildren_makes_available table position state revealState cache
        revealCache fuel revealRemaining revealed htableReveal hreveal).monoValues hvaluesLE

theorem resolveVerifierInput_makes_available_of_uncached_input
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (huncached : cache (.ordinary input) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((resolveVerifierInput parameter (.position position) input).run cache))) :
    TableInputAvailable table finalState (.position position) := by
  unfold resolveVerifierInput at hresult
  simp [StateT.run_get, huncached] at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hresolve⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hresolve
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealed, revealCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((resolveKnownInput parameter (.position position) input).run revealCache)
          revealState finalState revealRemaining remaining (output, finalCache) hresolve
      have htableReveal : ∀ coordinate cached,
          revealState.values coordinate = some cached → cached = table coordinate :=
        fun coordinate cached hcached =>
          htable coordinate cached (hvaluesLE coordinate cached hcached)
      exact (revealTableInputChildren_makes_available table position state revealState cache
        revealCache fuel revealRemaining revealed htableReveal hreveal).monoValues hvaluesLE

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

theorem Probe.outputCoordinate_eq_position_of_matchesInput'
    (probe : Probe) (parameter : PublicParameter) (input : HashInput)
    (hmatches : probe.MatchesInput parameter input) :
    ∃ position : Position, probe.outputCoordinate = .position position := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact ⟨.chain lay tree leafIdx chainIdx
        ⟨0, by norm_num [chainLength, winternitzBits]⟩, rfl⟩
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hnext : step.val + 1 < chainLength - 1
          · exact ⟨.chain lay tree leafIdx chainIdx ⟨step.val + 1, hnext⟩,
              by simp [Probe.outputCoordinate, hnext]⟩
          · exact ⟨.leaf lay tree leafIdx, by simp [Probe.outputCoordinate, hnext]⟩
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp [Probe.MatchesInput] at hmatches

theorem Probe.value_eq_table_of_output_available
    (table : Coordinate → HashOutput) (probe : Probe) (parameter : PublicParameter)
    (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (hmatches : probe.MatchesInput parameter input)
    (havailable : TableInputAvailable table state probe.outputCoordinate) :
    state.values probe.coordinate = some (table probe.coordinate) := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [Probe.outputCoordinate, TableInputAvailable] at havailable
      exact havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [Probe.outputCoordinate] at havailable ⊢
          by_cases hnext : step.val + 1 < chainLength - 1
          · rw [dif_pos hnext] at havailable
            have hnonzero : (⟨step.val + 1, hnext⟩ : ChainStep).val ≠ 0 := by
              change step.val + 1 ≠ 0
              omega
            simp only [TableInputAvailable, if_neg hnonzero] at havailable
            apply havailable (.chain lay tree leafIdx chainIdx step)
            rw [Position.mem_children_iff, Position.parentOf, dif_pos hnext]
          · rw [dif_neg hnext] at havailable
            simp only [TableInputAvailable] at havailable
            apply havailable (.chain lay tree leafIdx chainIdx step)
            rw [Position.mem_children_iff, Position.parentOf, dif_neg hnext]
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp [Probe.MatchesInput] at hmatches

theorem verifierHashQuery_not_done_of_fresh_correct_probe_of_opaque
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (probe : Probe) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hmatches : probe.MatchesInput parameter input)
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hvalue : state.values probe.coordinate = none)
    (hnotRevealed : probe.coordinate ∉ state.revealed)
    (huncached : cache (.ordinary input) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter input).run cache))) : False := by
  cases hdecode : decodeProbe? parameter input with
  | none => exact ((decodeProbe?_eq_none_iff parameter input).1 hdecode probe hmatches).elim
  | some candidate =>
      have hcandidateMatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
      have heq := Probe.matchesInput_unique parameter input hcandidateMatches hmatches
      subst candidate
      unfold verifierHashQuery at hresult
      rw [hdecode, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨probeRaw, hprobe, hresolve⟩ := hresult
      cases probeRaw with
      | stopped hit => simp at hresolve
      | done probeState probeRemaining probeResult =>
          rcases probeResult with ⟨probed, probeCache⟩
          change LazyRevealProbe.RawResult.done probeState probeRemaining
              (probed, probeCache) ∈ support
            (LazyRevealProbe.runRaw state fuel
              (LazyRevealProbe.probeQuery probe.coordinate probe.candidate >>= fun result =>
                pure (result, cache))) at hprobe
          rw [LazyRevealProbe.probeQuery,
            LazyRevealProbe.runRaw_probe_query_bind] at hprobe
          cases fuel with
          | zero => simp at hprobe
          | succ remainingFuel =>
              simp only at hprobe
              rw [if_neg hnotRevealed] at hprobe
              simp [LazyRevealProbe.runRaw] at hprobe
              rcases hprobe with ⟨rfl, rfl, rfl, rfl⟩
              obtain ⟨position, houtputPosition⟩ :=
                probe.outputCoordinate_eq_position_of_matchesInput' parameter input hmatches
              rw [houtputPosition] at hresolve
              have havailable := resolveVerifierInput_makes_available_of_uncached_input parameter
                table position input (state.addPending probe.coordinate probe.candidate) finalState
                  cache finalCache probeRemaining remaining output huncached htable hresolve
              rw [← houtputPosition] at havailable
              have hsourceValue := probe.value_eq_table_of_output_available table parameter input
                finalState hmatches havailable
              have hhit : (state.addPending probe.coordinate probe.candidate).hitAt
                  probe.coordinate (table probe.coordinate) := by
                rw [LazyRevealProbe.State.hitAt, ← hcandidate]
                exact LazyRevealProbe.State.pendingAt_addPending_self state probe.coordinate
                  probe.candidate
              have hpersist := LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done
                ((resolveVerifierInput parameter probe.outputCoordinate input).run cache)
                  probe.coordinate (table probe.coordinate)
                    (state.addPending probe.coordinate probe.candidate) finalState probeRemaining
                      remaining (output, finalCache) hvalue hhit (htable probe.coordinate) (by
                        simpa only [houtputPosition] using hresolve)
              rw [hpersist.1] at hsourceValue
              simp at hsourceValue

theorem verifierHashQuery_not_done_of_fresh_correct_probe
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (allowed : Coordinate → Prop) (probe : Probe) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hvalid : ChainState.ValidFor allowed state)
    (hmatches : probe.MatchesInput parameter input)
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hnotAllowed : ¬allowed probe.coordinate)
    (huncached : cache (.ordinary input) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter input).run cache))) : False := by
  have hchain := probe.isChainCoordinate_of_matchesInput hmatches
  exact verifierHashQuery_not_done_of_fresh_correct_probe_of_opaque parameter table probe
    input state finalState cache finalCache fuel remaining output hmatches hcandidate
      (hvalid.value_eq_none_of_not_allowed hchain hnotAllowed)
      (hvalid.not_revealed_of_not_allowed hchain hnotAllowed) huncached htable hresult

theorem simulateQ_verifierHashImpl_tweakableHash_not_done_of_fresh_correct_probe_of_opaque
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (probe : Probe)
    (domain : HashDomain) (payload : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter domain payload))
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hvalue : state.values probe.coordinate = none)
    (hnotRevealed : probe.coordinate ∉ state.revealed)
    (huncached : cache (.ordinary
      (tweakableHashInput parameter domain payload)) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter)
          (tweakableHash parameter domain payload)).run cache))) : False := by
  unfold tweakableHash oracleHash at hresult
  rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨queryRaw, hquery, hrest⟩ := hresult
  cases queryRaw with
  | stopped hit => simp at hrest
  | done queryState queryRemaining queryResult =>
      rcases queryResult with ⟨answer, queryCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((pure (truncateHash answer) : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) Digest).run queryCache)
          queryState finalState queryRemaining remaining (output, finalCache) hrest
      have htableQuery : ∀ coordinate cached,
          queryState.values coordinate = some cached → cached = table coordinate :=
        fun coordinate cached hcached =>
          htable coordinate cached (hvaluesLE coordinate cached hcached)
      have hquery' : LazyRevealProbe.RawResult.done queryState queryRemaining
          (answer, queryCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          ((verifierHashQuery parameter
            (tweakableHashInput parameter domain payload)).run cache)) := by
        simpa only [HasQuery.instOfMonadLift_query, simulateQ_spec_query,
          verifierHashImpl] using hquery
      exact verifierHashQuery_not_done_of_fresh_correct_probe_of_opaque parameter table probe
        (tweakableHashInput parameter domain payload) state queryState cache queryCache fuel
          queryRemaining answer hmatches hcandidate hvalue hnotRevealed huncached htableQuery hquery'

theorem simulateQ_verifierHashImpl_tweakableHash_not_done_of_fresh_correct_probe
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (allowed : Coordinate → Prop) (probe : Probe)
    (domain : HashDomain) (payload : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : Digest)
    (hvalid : ChainState.ValidFor allowed state)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter domain payload))
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hnotAllowed : ¬allowed probe.coordinate)
    (huncached : cache (.ordinary
      (tweakableHashInput parameter domain payload)) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter)
          (tweakableHash parameter domain payload)).run cache))) : False := by
  have hchain := probe.isChainCoordinate_of_matchesInput hmatches
  exact simulateQ_verifierHashImpl_tweakableHash_not_done_of_fresh_correct_probe_of_opaque
    parameter table probe domain payload state finalState cache finalCache fuel remaining output
      hmatches hcandidate (hvalid.value_eq_none_of_not_allowed hchain hnotAllowed)
      (hvalid.not_revealed_of_not_allowed hchain hnotAllowed) huncached htable hresult

theorem simulateQ_verifierHashImpl_chainWalk_not_done_of_fresh_correct_probe_of_opaque
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (initialValue : Digest)
    (hpositive : 0 < steps) (hrange : start + steps ≤ chainLength - 1)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨start, by omega⟩) (digestBytes initialValue)))
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hvalue : state.values probe.coordinate = none)
    (hnotRevealed : probe.coordinate ∉ state.revealed)
    (huncached : cache (.ordinary
      (tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨start, by omega⟩)
          (digestBytes initialValue))) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter)
          (chainWalk parameter lay tree leafIdx chainIdx start steps initialValue)).run cache))) :
    False := by
  induction steps generalizing state finalState cache finalCache fuel remaining output with
  | zero => omega
  | succ steps ih =>
      cases steps with
      | zero =>
          have hstep : start < chainLength - 1 := by omega
          rw [chainWalk, chainWalk, pure_bind, Nat.add_zero, dif_pos hstep] at hresult
          exact simulateQ_verifierHashImpl_tweakableHash_not_done_of_fresh_correct_probe_of_opaque
            parameter table probe
              (.chain lay tree leafIdx chainIdx ⟨start, hstep⟩)
                (digestBytes initialValue) state finalState cache finalCache fuel remaining
                  output (by simpa only using hmatches) hcandidate hvalue hnotRevealed (by
                    simpa only using huncached) htable hresult
      | succ previous =>
          rw [chainWalk, simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨prefixRaw, hprefix, hrest⟩ := hresult
          cases prefixRaw with
          | stopped hit => simp at hrest
          | done prefixState prefixRemaining prefixResult =>
              rcases prefixResult with ⟨prefixValue, prefixCache⟩
              simp only at hrest
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done _ prefixState
                finalState prefixRemaining remaining (output, finalCache) hrest
              have htablePrefix : ∀ coordinate cached,
                  prefixState.values coordinate = some cached → cached = table coordinate :=
                fun coordinate cached hcached =>
                  htable coordinate cached (hvaluesLE coordinate cached hcached)
              exact ih (by omega) (by omega) state prefixState cache prefixCache fuel
                prefixRemaining prefixValue hmatches hvalue hnotRevealed huncached htablePrefix
                  hprefix

theorem simulateQ_verifierHashImpl_chainWalk_not_done_of_fresh_correct_probe
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (allowed : Coordinate → Prop) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (initialValue : Digest)
    (hpositive : 0 < steps) (hrange : start + steps ≤ chainLength - 1)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : Digest)
    (hvalid : ChainState.ValidFor allowed state)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨start, by omega⟩) (digestBytes initialValue)))
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hnotAllowed : ¬allowed probe.coordinate)
    (huncached : cache (.ordinary
      (tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨start, by omega⟩)
          (digestBytes initialValue))) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter)
          (chainWalk parameter lay tree leafIdx chainIdx start steps initialValue)).run cache))) :
    False := by
  have hchain := probe.isChainCoordinate_of_matchesInput hmatches
  exact simulateQ_verifierHashImpl_chainWalk_not_done_of_fresh_correct_probe_of_opaque
    parameter table probe lay tree leafIdx chainIdx start steps initialValue hpositive hrange state
      finalState cache finalCache fuel remaining output hmatches hcandidate
      (hvalid.value_eq_none_of_not_allowed hchain hnotAllowed)
      (hvalid.not_revealed_of_not_allowed hchain hnotAllowed) huncached htable hresult

def PreservesCoordinate (coordinate : Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
      finalState.values coordinate = state.values coordinate ∧
        (coordinate ∈ finalState.revealed ↔ coordinate ∈ state.revealed)

theorem PreservesCoordinate.bind
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesCoordinate coordinate left)
    (hnext : ∀ value, PreservesCoordinate coordinate (next value)) :
    PreservesCoordinate coordinate (left >>= next) := by
  intro state cache fuel finalState remaining result finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun leftResult => (next leftResult.1).run leftResult.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining leftResult =>
      rcases leftResult with ⟨leftValue, middleCache⟩
      have hmiddle := hleft state cache fuel middleState middleRemaining leftValue middleCache hraw
      have hfinal := hnext leftValue middleState middleCache middleRemaining finalState remaining
        result finalCache hrest
      exact ⟨hfinal.1.trans hmiddle.1, hfinal.2.trans hmiddle.2⟩

theorem preservesCoordinate_pure (coordinate : Coordinate) (value : alpha) :
    PreservesCoordinate coordinate
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, Iff.rfl⟩

theorem preservesCoordinate_splitHashQuery (coordinate : Coordinate) (key : SplitHashKey) :
    PreservesCoordinate coordinate (splitHashQuery key) := by
  intro state cache fuel finalState remaining value finalCache hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache key with
  | some output =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, Iff.rfl⟩
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.hashOutputQuery >>= fun output =>
            pure (output, Function.update cache key (some output)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery, LazyRevealProbe.runRaw_hashOutput_query_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, Iff.rfl⟩

theorem preservesCoordinate_probe (coordinate : Coordinate) (candidate : Probe) :
    PreservesCoordinate coordinate (probe candidate) := by
  intro state cache fuel finalState remaining value finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun output =>
        pure (output, cache))) at hresult
  rw [LazyRevealProbe.probeQuery, LazyRevealProbe.runRaw_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remainingFuel =>
      simp only at hresult
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · rw [if_pos hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨rfl, Iff.rfl⟩
      · rw [if_neg hrevealed] at hresult
        simp [LazyRevealProbe.runRaw] at hresult
        rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
        simp [LazyRevealProbe.State.addPending]

theorem preservesCoordinate_revealCoordinateOutput_of_ne
    (coordinate other : Coordinate) (hne : coordinate ≠ other) :
    PreservesCoordinate coordinate (revealCoordinateOutput other) := by
  intro state cache fuel finalState remaining value finalCache hresult
  rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values other with
  | some output =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, Iff.rfl⟩
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hrest⟩ := hresult
      by_cases hhit : state.hitAt other output
      · rw [if_pos hhit] at hrest
        simp at hrest
      · rw [if_neg hhit] at hrest
        simp [LazyRevealProbe.runRaw] at hrest
        rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
        simp [LazyRevealProbe.State.materialize, Function.update, hne]

theorem preservesCoordinate_publishCoordinate_of_ne
    (coordinate other : Coordinate) (hne : coordinate ≠ other) :
    PreservesCoordinate coordinate (publishCoordinate other) := by
  intro state cache fuel finalState remaining value finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.publishQuery other >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, LazyRevealProbe.runRaw_publish_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  simp [LazyRevealProbe.State.publish, hne]

theorem preservesCoordinate_revealCoordinate_of_ne
    (coordinate other : Coordinate) (hne : coordinate ≠ other) :
    PreservesCoordinate coordinate (revealCoordinate other) := by
  unfold revealCoordinate
  exact (preservesCoordinate_revealCoordinateOutput_of_ne coordinate other hne).bind fun _ =>
    preservesCoordinate_pure coordinate _

theorem preservesCoordinate_revealPosition_of_ne
    (coordinate : Coordinate) (position : Position)
    (hne : coordinate ≠ .position position) :
    PreservesCoordinate coordinate (revealPosition position) := by
  simpa only [revealPosition] using
    preservesCoordinate_revealCoordinate_of_ne coordinate (.position position) hne

theorem preservesCoordinate_revealPositionValues
    (coordinate : Coordinate) (positions : List Position)
    (hne : ∀ position, position ∈ positions → coordinate ≠ .position position) :
    PreservesCoordinate coordinate (revealPositionValues positions) := by
  induction positions with
  | nil => exact preservesCoordinate_pure coordinate []
  | cons position remaining ih =>
      rw [revealPositionValues]
      exact (preservesCoordinate_revealPosition_of_ne coordinate position
        (hne position (by simp))).bind fun value =>
          (ih (fun other hother => hne other (by simp [hother]))).bind fun values =>
            preservesCoordinate_pure coordinate (value :: values)

theorem RawReadOnly.preservesCoordinate
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hreadonly : RawReadOnly computation) (coordinate : Coordinate) :
    PreservesCoordinate coordinate computation := by
  intro state cache fuel finalState remaining value finalCache hresult
  obtain ⟨rfl, _, _⟩ := hreadonly state cache fuel finalState remaining value finalCache hresult
  exact ⟨rfl, Iff.rfl⟩

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

theorem PreservesPublishedValues.pure (value : alpha) :
    PreservesPublishedValues
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hpublished hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hpublished

theorem PreservesPublishedValues.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesPublishedValues left)
    (hnext : ∀ value, PreservesPublishedValues (next value)) :
    PreservesPublishedValues (left >>= next) := by
  intro state cache fuel finalState remaining value finalCache hpublished hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      exact hnext middleValue middleState middleCache middleRemaining finalState remaining value
        finalCache (hleft state cache fuel middleState middleRemaining middleValue middleCache
          hpublished hraw) hrest

theorem PreservesPublishedValues.sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, PreservesPublishedValues (computation index)) :
    PreservesPublishedValues (sequenceFin computation) := by
  induction n with
  | zero => exact PreservesPublishedValues.pure Fin.elim0
  | succ n ih =>
      rw [SphincsSecurity.Concrete.sequenceFin]
      exact (hcomputation 0).bind fun _ =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun _ =>
            PreservesPublishedValues.pure _

def PreservesPublishedValuesImpl {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, PreservesPublishedValues (impl query)

theorem PreservesPublishedValuesImpl.simulateQ {spec : OracleSpec ι}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : PreservesPublishedValuesImpl impl)
    (computation : OracleComp spec alpha) :
    PreservesPublishedValues (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact PreservesPublishedValues.pure value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

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

theorem RawReadOnly.preservesPublishedValues
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hreadonly : RawReadOnly computation) : PreservesPublishedValues computation :=
  PreservesPublishedValues.of_preservesCoordinate hreadonly.preservesCoordinate

theorem preservesPublishedValues_ensureCoordinate (coordinate : Coordinate) :
    PreservesPublishedValues (ensureCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hpublished hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.ensureQuery coordinate >>= fun result => pure (result, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery, LazyRevealProbe.runRaw_ensure_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  simpa [PublishedValues, LazyRevealProbe.State.ensure] using hpublished

theorem preservesPublishedValues_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec alpha) :
    PreservesPublishedValues (simulateQ ordinaryHashImpl computation) := by
  intro state cache fuel finalState remaining value finalCache hpublished hresult
  rw [(mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state finalState cache
    finalCache fuel remaining value hresult).1]
  exact hpublished

theorem preservesPublishedValues_simulateQ_splitUniformImpl
    (computation : ProbComp alpha) :
    PreservesPublishedValues (simulateQ splitUniformImpl computation) := by
  intro state cache fuel finalState remaining value finalCache hpublished hresult
  rw [(mem_runRaw_simulateQ_splitUniformImpl_projects computation state finalState cache
    finalCache fuel remaining value hresult).1]
  exact hpublished

theorem preservesPublishedValues_revealCoordinateOutput (coordinate : Coordinate) :
    PreservesPublishedValues (revealCoordinateOutput coordinate) := by
  intro state cache fuel finalState remaining value finalCache hpublished hresult
  rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some output =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hpublished
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨output, _, hrest⟩ := hresult
      by_cases hhit : state.hitAt coordinate output
      · rw [if_pos hhit] at hrest
        simp at hrest
      · rw [if_neg hhit] at hrest
        simp [LazyRevealProbe.runRaw] at hrest
        rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
        intro other hrevealed
        have hvalueOther := hpublished other (by
          simpa [LazyRevealProbe.State.materialize] using hrevealed)
        by_cases heq : other = coordinate
        · subst other
          simp [LazyRevealProbe.State.materialize]
        · simpa [LazyRevealProbe.State.materialize, Function.update, heq] using hvalueOther

theorem preservesPublishedValues_revealCoordinate (coordinate : Coordinate) :
    PreservesPublishedValues (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (preservesPublishedValues_revealCoordinateOutput coordinate).bind fun _ =>
    PreservesPublishedValues.pure _

theorem preservesPublishedValues_revealPublishedCoordinate (coordinate : Coordinate) :
    PreservesPublishedValues (revealPublishedCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hpublished hresult
  unfold revealPublishedCoordinate at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hrest⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealedValue, revealCache⟩
      have hpublishedReveal := preservesPublishedValues_revealCoordinate coordinate state cache
        fuel revealState revealRemaining revealedValue revealCache hpublished hreveal
      obtain ⟨coordinateOutput, _, hcoordinateValue⟩ :=
        mem_runRaw_revealCoordinate_value coordinate state revealState cache revealCache fuel
          revealRemaining revealedValue hreveal
      change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
        (LazyRevealProbe.runRaw revealState revealRemaining
          ((publishCoordinate coordinate).run revealCache >>= fun publishResult =>
            (pure revealedValue : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) Digest).run publishResult.2)) at hrest
      rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hrest
      obtain ⟨publishRaw, hpublish, hreturn⟩ := hrest
      cases publishRaw with
      | stopped hit => simp at hreturn
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          change LazyRevealProbe.RawResult.done publishState publishRemaining
              (publishedUnit, publishCache) ∈ support
            (LazyRevealProbe.runRaw revealState revealRemaining
              (LazyRevealProbe.publishQuery coordinate >>= fun result =>
                pure (result, revealCache))) at hpublish
          rw [LazyRevealProbe.publishQuery, LazyRevealProbe.runRaw_publish_query_bind] at hpublish
          simp [LazyRevealProbe.runRaw] at hpublish
          rcases hpublish with ⟨rfl, rfl, rfl, rfl⟩
          simp [LazyRevealProbe.runRaw] at hreturn
          rcases hreturn with ⟨rfl, rfl, rfl, rfl⟩
          intro other hother
          by_cases heq : other = coordinate
          · subst other
            change revealState.values coordinate ≠ none
            rw [hcoordinateValue]
            simp
          · apply hpublishedReveal other
            simpa [LazyRevealProbe.State.publish, heq] using hother

theorem publishedValues_of_mem_runRaw_publishCoordinate
    (coordinate : Coordinate) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : Unit)
    (hpublished : PublishedValues state)
    (hvalue : state.values coordinate ≠ none)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((publishCoordinate coordinate).run cache))) :
    PublishedValues finalState := by
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.publishQuery coordinate >>= fun result => pure (result, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, LazyRevealProbe.runRaw_publish_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  intro other hother
  by_cases heq : other = coordinate
  · subst other
    change state.values coordinate ≠ none
    exact hvalue
  · apply hpublished other
    simpa [LazyRevealProbe.State.publish, heq] using hother

theorem preservesCoordinate_get (coordinate : Coordinate) :
    PreservesCoordinate coordinate
      (get : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) SplitHashCache) := by
  intro state cache fuel finalState remaining value finalCache hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, Iff.rfl⟩

theorem preservesCoordinate_modify (coordinate : Coordinate)
    (update : SplitHashCache → SplitHashCache) :
    PreservesCoordinate coordinate
      (modify update : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro state cache fuel finalState remaining value finalCache hresult
  simp [StateT.run_modify, LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, Iff.rfl⟩

theorem preservesCoordinate_resolveKnownInput_of_ne
    (parameter : PublicParameter) (coordinate other : Coordinate) (input : HashInput)
    (hne : coordinate ≠ other) :
    PreservesCoordinate coordinate (resolveKnownInput parameter other input) := by
  unfold resolveKnownInput
  exact (rawReadOnly_peekTableInput parameter other).preservesCoordinate coordinate |>.bind
    fun known => match known with
    | none => preservesCoordinate_splitHashQuery coordinate (.ordinary input)
    | some knownInput => by
        simp only
        by_cases heq : knownInput = input
        · rw [if_pos heq]
          exact (preservesCoordinate_revealCoordinateOutput_of_ne coordinate other hne).bind
            fun _ => (preservesCoordinate_publishCoordinate_of_ne coordinate other hne).bind
              fun _ => (preservesCoordinate_modify coordinate fun cache =>
                Function.update cache (.ordinary input) (some _)).bind fun _ =>
                  preservesCoordinate_pure coordinate _
        · rw [if_neg heq]
          exact preservesCoordinate_splitHashQuery coordinate (.ordinary input)

theorem preservesPublishedValues_revealCoordinateOutput_publish (coordinate : Coordinate) :
    PreservesPublishedValues (do
      let output ← revealCoordinateOutput coordinate
      publishCoordinate coordinate
      pure output) := by
  intro state cache fuel finalState remaining value finalCache hpublished hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealRaw, hreveal, hrest⟩ := hresult
  cases revealRaw with
  | stopped hit => simp at hrest
  | done revealState revealRemaining revealResult =>
      rcases revealResult with ⟨revealedOutput, revealCache⟩
      have hpublishedReveal := preservesPublishedValues_revealCoordinateOutput coordinate state
        cache fuel revealState revealRemaining revealedOutput revealCache hpublished hreveal
      have hcoordinateValue := (mem_runRaw_revealCoordinateOutput_value coordinate state
        revealState cache revealCache fuel revealRemaining revealedOutput hreveal).1
      simp [publishCoordinate, LazyRevealProbe.publishQuery,
        LazyRevealProbe.runRaw] at hrest
      rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
      intro other hother
      by_cases heq : other = coordinate
      · subst other
        change revealState.values coordinate ≠ none
        rw [hcoordinateValue]
        simp
      · apply hpublishedReveal other
        simpa [LazyRevealProbe.State.publish, heq] using hother

theorem preservesPublishedValues_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    PreservesPublishedValues (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  exact (rawReadOnly_peekTableInput parameter coordinate).preservesPublishedValues.bind
    fun known => match known with
    | none => PreservesPublishedValues.of_preservesCoordinate fun other =>
        preservesCoordinate_splitHashQuery other (.ordinary input)
    | some knownInput => by
        simp only
        by_cases heq : knownInput = input
        · rw [if_pos heq]
          have hpreserves :=
            (preservesPublishedValues_revealCoordinateOutput_publish coordinate).bind
              fun output =>
                (PreservesPublishedValues.of_preservesCoordinate fun other =>
                  preservesCoordinate_modify other fun cache =>
                    Function.update cache (.ordinary input) (some output)).bind fun _ =>
                      PreservesPublishedValues.pure output
          simpa only [bind_assoc, pure_bind] using hpreserves
        · rw [if_neg heq]
          exact PreservesPublishedValues.of_preservesCoordinate fun other =>
            preservesCoordinate_splitHashQuery other (.ordinary input)

theorem preservesPublishedValues_probeFirstMissingInputCoordinate (input : HashInput) :
    ∀ slot coordinates,
      PreservesPublishedValues (probeFirstMissingInputCoordinate input slot coordinates)
  | _, [] => PreservesPublishedValues.pure ()
  | slot, coordinate :: remaining => by
      rw [probeFirstMissingInputCoordinate]
      exact (rawReadOnly_peekCoordinate coordinate).preservesPublishedValues.bind fun value =>
        match value with
        | none => PreservesPublishedValues.of_preservesCoordinate fun other =>
            preservesCoordinate_probe other ⟨coordinate, slotDigest slot input⟩
        | some _ => preservesPublishedValues_probeFirstMissingInputCoordinate input
            (slot + 1) remaining

theorem preservesPublishedValues_prepareLeafInputProbe
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesPublishedValues (prepareLeafInputProbe input candidate lay tree leafIdx) := by
  unfold prepareLeafInputProbe
  apply (rawReadOnly_peekCoordinate candidate.coordinate).preservesPublishedValues.bind
  intro value
  cases value with
  | none =>
      simp only
      exact PreservesPublishedValues.of_preservesCoordinate fun coordinate =>
        preservesCoordinate_probe coordinate candidate
  | some output =>
      simp only
      exact preservesPublishedValues_probeFirstMissingInputCoordinate input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem preservesPublishedValues_probingHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    PreservesPublishedValues (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases decodePosition? parameter input with
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (preservesPublishedValues_prepareLeafInputProbe input candidate lay tree
                leafIdx).bind fun _ => preservesPublishedValues_resolveKnownInput parameter
                  candidate.outputCoordinate input
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact (PreservesPublishedValues.of_preservesCoordinate fun coordinate =>
                preservesCoordinate_probe coordinate candidate).bind fun _ =>
                  preservesPublishedValues_resolveKnownInput parameter
                    candidate.outputCoordinate input
      | none => exact (PreservesPublishedValues.of_preservesCoordinate fun coordinate =>
          preservesCoordinate_probe coordinate candidate).bind fun _ =>
            preservesPublishedValues_resolveKnownInput parameter candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact PreservesPublishedValues.of_preservesCoordinate fun coordinate =>
          preservesCoordinate_splitHashQuery coordinate (.ordinary input)
      | some position =>
          cases position with
          | chain | leaf => exact preservesPublishedValues_resolveKnownInput parameter _ input
          | node lay tree level nodeIdx =>
              exact (preservesPublishedValues_probeFirstMissingInputCoordinate input 0
                ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).bind
                  fun _ => preservesPublishedValues_resolveKnownInput parameter _ input
          | ftsLeaf | ftsNode | ftsRoots =>
              exact PreservesPublishedValues.of_preservesCoordinate fun coordinate =>
                preservesCoordinate_splitHashQuery coordinate (.ordinary input)

theorem preservesPublishedValues_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    PreservesPublishedValues (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (PreservesPublishedValues.sequenceFin _ fun step =>
    preservesPublishedValues_ensureCoordinate
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        PreservesPublishedValues.pure ()

theorem preservesPublishedValues_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    PreservesPublishedValues (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (PreservesPublishedValues.sequenceFin _ fun step => by
    split
    · exact preservesPublishedValues_ensureCoordinate
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact PreservesPublishedValues.pure ()).bind fun _ =>
        PreservesPublishedValues.pure ()

theorem preservesPublishedValues_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesPublishedValues (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (PreservesPublishedValues.sequenceFin _ fun chainIdx =>
    preservesPublishedValues_ensureFullChain lay tree leafIdx chainIdx).bind fun _ =>
      preservesPublishedValues_ensureCoordinate (.position (.leaf lay tree leafIdx))

theorem preservesPublishedValues_ensureTreeNode (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, PreservesPublishedValues (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact preservesPublishedValues_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (preservesPublishedValues_ensureTreeNode lay tree level (2 * nodeIdx)).bind fun _ =>
        (preservesPublishedValues_ensureTreeNode lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact preservesPublishedValues_ensureCoordinate _
          · exact PreservesPublishedValues.pure ()

theorem preservesPublishedValues_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    PreservesPublishedValues (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (preservesPublishedValues_ensureTreeNode lay tree 0 nodeIdx).bind fun _ =>
        preservesPublishedValues_revealCoordinate _
  | succ current =>
      rw [maskedTreeNode]
      exact (preservesPublishedValues_ensureTreeNode lay tree (current + 1) nodeIdx).bind fun _ => by
        by_cases hlevel : current < maxLayerHeight
        · rw [dif_pos hlevel]
          exact preservesPublishedValues_revealCoordinate _
        · rw [dif_neg hlevel]
          exact PreservesPublishedValues.pure 0

theorem preservesPublishedValues_maskedTreeRoot (lay : Layer) (tree : TreeIndex) :
    PreservesPublishedValues (maskedTreeRoot lay tree) :=
  preservesPublishedValues_maskedTreeNode lay tree (layerHeight lay) 0

theorem preservesPublishedValues_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesPublishedValues (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (PreservesPublishedValues.sequenceFin _ fun level => by
    split
    · exact preservesPublishedValues_ensureTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact PreservesPublishedValues.pure ()).bind fun _ =>
        PreservesPublishedValues.pure ()

theorem preservesPublishedValues_revealPositionValues :
    ∀ positions, PreservesPublishedValues (revealPositionValues positions)
  | [] => PreservesPublishedValues.pure []
  | position :: remaining => by
      rw [revealPositionValues]
      exact (preservesPublishedValues_revealCoordinate (.position position)).bind fun value =>
        (preservesPublishedValues_revealPositionValues remaining).bind fun values =>
          PreservesPublishedValues.pure (value :: values)

theorem preservesPublishedValues_revealTableInputChildren (coordinate : Coordinate) :
    PreservesPublishedValues (revealTableInputChildren coordinate) := by
  cases coordinate with
  | chainStart => exact PreservesPublishedValues.pure ()
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hzero : step.val = 0
          · simp only [revealTableInputChildren, hzero, ↓reduceIte]
            exact (preservesPublishedValues_revealCoordinate
              (.chainStart lay tree leafIdx chainIdx)).bind fun _ =>
                PreservesPublishedValues.pure ()
          · simp only [revealTableInputChildren, hzero, ↓reduceIte]
            exact (preservesPublishedValues_revealPositionValues _).bind fun _ =>
              PreservesPublishedValues.pure ()
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [revealTableInputChildren]
          exact (preservesPublishedValues_revealPositionValues _).bind fun _ =>
            PreservesPublishedValues.pure ()

theorem preservesPublishedValues_resolveVerifierInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    PreservesPublishedValues (resolveVerifierInput parameter coordinate input) := by
  unfold resolveVerifierInput
  exact (PreservesPublishedValues.of_preservesCoordinate preservesCoordinate_get).bind fun cache =>
    match cache (.ordinary input) with
    | some output => PreservesPublishedValues.pure output
    | none => (preservesPublishedValues_revealTableInputChildren coordinate).bind fun _ =>
        preservesPublishedValues_resolveKnownInput parameter coordinate input

theorem preservesPublishedValues_verifierHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    PreservesPublishedValues (verifierHashQuery parameter input) := by
  unfold verifierHashQuery
  cases decodeProbe? parameter input with
  | some candidate =>
      exact (PreservesPublishedValues.of_preservesCoordinate fun coordinate =>
        preservesCoordinate_probe coordinate candidate).bind fun _ =>
          preservesPublishedValues_resolveVerifierInput parameter candidate.outputCoordinate input
  | none =>
      cases decodePosition? parameter input with
      | none => exact PreservesPublishedValues.of_preservesCoordinate fun coordinate =>
          preservesCoordinate_splitHashQuery coordinate (.ordinary input)
      | some position =>
          cases position with
          | chain | leaf | node => exact preservesPublishedValues_resolveVerifierInput parameter _ input
          | ftsLeaf | ftsNode | ftsRoots =>
              exact PreservesPublishedValues.of_preservesCoordinate fun coordinate =>
                preservesCoordinate_splitHashQuery coordinate (.ordinary input)

def CoordinateChildrenAvoid (coordinate : Coordinate) : Coordinate → Prop
  | .chainStart _ _ _ _ => True
  | .position position@(.chain lay tree leafIdx chainIdx step) =>
      if step.val = 0 then coordinate ≠ .chainStart lay tree leafIdx chainIdx
      else ∀ child, child ∈ position.children → coordinate ≠ .position child
  | .position position =>
      ∀ child, child ∈ position.children → coordinate ≠ .position child

theorem preservesCoordinate_revealTableInputChildren
    (coordinate other : Coordinate)
    (hne : CoordinateChildrenAvoid coordinate other) :
    PreservesCoordinate coordinate (revealTableInputChildren other) := by
  cases other with
  | chainStart => exact preservesCoordinate_pure coordinate ()
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hzero : step.val = 0
          · simp only [revealTableInputChildren, hzero, ↓reduceIte]
            exact (preservesCoordinate_revealCoordinate_of_ne coordinate
              (.chainStart lay tree leafIdx chainIdx)
                (by simpa [CoordinateChildrenAvoid, hzero] using hne)).bind fun _ =>
                preservesCoordinate_pure coordinate ()
          · simp only [revealTableInputChildren, hzero, ↓reduceIte]
            exact (preservesCoordinate_revealPositionValues coordinate _
              (by simpa [CoordinateChildrenAvoid, hzero] using hne)).bind fun _ =>
                preservesCoordinate_pure coordinate ()
      | leaf lay tree leafIdx =>
          simp only [revealTableInputChildren]
          exact (preservesCoordinate_revealPositionValues coordinate _ hne).bind fun _ =>
            preservesCoordinate_pure coordinate ()
      | node lay tree level nodeIdx =>
          simp only [revealTableInputChildren]
          exact (preservesCoordinate_revealPositionValues coordinate _ hne).bind fun _ =>
            preservesCoordinate_pure coordinate ()
      | ftsLeaf index tree leafIdx =>
          simp only [revealTableInputChildren]
          exact (preservesCoordinate_revealPositionValues coordinate _ hne).bind fun _ =>
            preservesCoordinate_pure coordinate ()
      | ftsNode index tree level nodeIdx =>
          simp only [revealTableInputChildren]
          exact (preservesCoordinate_revealPositionValues coordinate _ hne).bind fun _ =>
            preservesCoordinate_pure coordinate ()
      | ftsRoots index =>
          simp only [revealTableInputChildren]
          exact (preservesCoordinate_revealPositionValues coordinate _ hne).bind fun _ =>
            preservesCoordinate_pure coordinate ()

theorem preservesCoordinate_resolveVerifierInput
    (parameter : PublicParameter) (coordinate other : Coordinate) (input : HashInput)
    (hchildren : CoordinateChildrenAvoid coordinate other)
    (hother : coordinate ≠ other) :
    PreservesCoordinate coordinate (resolveVerifierInput parameter other input) := by
  unfold resolveVerifierInput
  exact (preservesCoordinate_get coordinate).bind fun cache =>
    match cache (.ordinary input) with
    | some output => preservesCoordinate_pure coordinate output
    | none => (preservesCoordinate_revealTableInputChildren coordinate other hchildren).bind
        fun _ => preservesCoordinate_resolveKnownInput_of_ne parameter coordinate other input hother

theorem Probe.coordinate_eq_chain_source_of_matchesInput
    (probe : Probe) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (payload : HashInput)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step) payload)) :
    probe.coordinate = .chainStart lay tree leafIdx chainIdx ∨
      ∃ previous : ChainStep,
        probe.coordinate = .position (.chain lay tree leafIdx chainIdx previous) := by
  rcases probe with ⟨coordinate, candidate⟩
  cases coordinate with
  | chainStart sourceLay sourceTree sourceLeaf sourceChain =>
      obtain ⟨sourceStep, _, hinput⟩ := hmatches
      have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial)
        hinput.symm).1
      cases hdomain
      exact Or.inl rfl
  | position position =>
      cases position with
      | chain sourceLay sourceTree sourceLeaf sourceChain sourceStep =>
          simp only [Probe.MatchesInput] at hmatches
          split at hmatches
          · obtain ⟨nextStep, _, hinput⟩ := hmatches
            have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial)
              hinput.symm).1
            cases hdomain
            exact Or.inr ⟨sourceStep, rfl⟩
          · obtain ⟨_, sourcePayload, hinput, _⟩ := hmatches
            have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial)
              hinput.symm).1
            cases hdomain
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp [Probe.MatchesInput] at hmatches

theorem Probe.coordinate_ne_of_matches_chain_ne
    (probe : Probe) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (payload : HashInput)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step) payload))
    (otherChain : ChainIndex) (hne : otherChain ≠ chainIdx) :
    probe.coordinate ≠ .chainStart lay tree leafIdx otherChain ∧
      (∀ otherStep : ChainStep,
        probe.coordinate ≠ .position (.chain lay tree leafIdx otherChain otherStep)) := by
  rcases probe.coordinate_eq_chain_source_of_matchesInput parameter lay tree leafIdx chainIdx
    step payload hmatches with hstart | ⟨previous, hprevious⟩
  · rw [hstart]
    constructor
    · intro heq
      exact hne (Coordinate.chainStart.inj heq).2.2.2.symm
    · intro otherStep heq
      cases heq
  · rw [hprevious]
    constructor
    · intro heq
      cases heq
    · intro otherStep heq
      exact hne (Position.chain.inj (Coordinate.position.inj heq)).2.2.2.1.symm

theorem Probe.coordinate_ne_chainStart_of_matches_chain_layer_ne
    (probe : Probe) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (payload : HashInput)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step) payload))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (otherChain : ChainIndex) (hne : otherLay ≠ lay) :
    probe.coordinate ≠ .chainStart otherLay otherTree otherLeaf otherChain := by
  rcases probe.coordinate_eq_chain_source_of_matchesInput parameter lay tree leafIdx chainIdx
    step payload hmatches with hsource | ⟨previous, hsource⟩ <;> rw [hsource]
  · intro heq
    exact hne (Coordinate.chainStart.inj heq).1.symm
  · intro heq
    cases heq

theorem Probe.coordinate_ne_position_chain_of_matches_chain_layer_ne
    (probe : Probe) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (payload : HashInput)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step) payload))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (otherChain : ChainIndex) (otherStep : ChainStep) (hne : otherLay ≠ lay) :
    probe.coordinate ≠ .position
      (.chain otherLay otherTree otherLeaf otherChain otherStep) := by
  rcases probe.coordinate_eq_chain_source_of_matchesInput parameter lay tree leafIdx chainIdx
    step payload hmatches with hsource | ⟨previous, hsource⟩ <;> rw [hsource]
  · intro heq
    cases heq
  · intro heq
    exact hne (Position.chain.inj (Coordinate.position.inj heq)).1.symm

theorem Probe.coordinate_ne_position_leaf_of_matches_chain_layer_ne
    (probe : Probe) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (payload : HashInput)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step) payload))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (_hne : otherLay ≠ lay) :
    probe.coordinate ≠ .position (.leaf otherLay otherTree otherLeaf) := by
  rcases probe.coordinate_eq_chain_source_of_matchesInput parameter lay tree leafIdx chainIdx
    step payload hmatches with hsource | ⟨previous, hsource⟩ <;> rw [hsource] <;>
      intro heq <;> cases heq

theorem Probe.coordinate_ne_position_node_of_matches_chain_layer_ne
    (probe : Probe) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (payload : HashInput)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step) payload))
    (otherLay : Layer) (otherTree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) (_hne : otherLay ≠ lay) :
    probe.coordinate ≠ .position (.node otherLay otherTree level nodeIdx) := by
  rcases probe.coordinate_eq_chain_source_of_matchesInput parameter lay tree leafIdx chainIdx
    step payload hmatches with hsource | ⟨previous, hsource⟩ <;> rw [hsource] <;>
      intro heq <;> cases heq

theorem preservesCoordinate_verifierHashQuery_at_position
    (parameter : PublicParameter) (coordinate : Coordinate)
    (position : Position) (input : HashInput)
    (hat : AtPosition parameter input position)
    (hots : IsOtsPosition position)
    (hchildren : CoordinateChildrenAvoid coordinate (.position position))
    (hother : coordinate ≠ .position position) :
    PreservesCoordinate coordinate (verifierHashQuery parameter input) := by
  have hposition : decodePosition? parameter input = some position :=
    (decodePosition?_eq_some_iff parameter input position).2 hat
  cases hdecode : decodeProbe? parameter input with
  | none =>
      unfold verifierHashQuery
      rw [hdecode, hposition]
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          exact preservesCoordinate_resolveVerifierInput parameter coordinate
            (.position (.chain lay tree leafIdx chainIdx step)) input hchildren hother
      | leaf lay tree leafIdx =>
          exact preservesCoordinate_resolveVerifierInput parameter coordinate
            (.position (.leaf lay tree leafIdx)) input hchildren hother
      | node lay tree level nodeIdx =>
          exact preservesCoordinate_resolveVerifierInput parameter coordinate
            (.position (.node lay tree level nodeIdx)) input hchildren hother
      | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots
  | some candidate =>
      have houtput := candidate.outputCoordinate_eq_position_of_matchesInput parameter input
        position ((decodeProbe?_eq_some_iff parameter input candidate).1 hdecode) hat
      unfold verifierHashQuery
      rw [hdecode]
      exact (preservesCoordinate_probe coordinate candidate).bind fun _ => by
        rw [houtput]
        exact preservesCoordinate_resolveVerifierInput parameter coordinate (.position position)
          input hchildren hother

theorem preservesCoordinate_verifierHashQuery_chain_of_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx otherChain : ChainIndex) (targetStep currentStep : ChainStep)
    (targetValue currentValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (hne : otherChain ≠ chainIdx) :
    PreservesCoordinate probe.coordinate
      (verifierHashQuery parameter
        (tweakableHashInput parameter (.chain lay tree leafIdx otherChain currentStep)
          (digestBytes currentValue))) := by
  let input := tweakableHashInput parameter (.chain lay tree leafIdx otherChain currentStep)
    (digestBytes currentValue)
  have htargetNe := probe.coordinate_ne_of_matches_chain_ne parameter lay tree leafIdx chainIdx
    targetStep (digestBytes targetValue) hmatches otherChain hne
  have hposition : decodePosition? parameter input =
      some (.chain lay tree leafIdx otherChain currentStep) :=
    (decodePosition?_eq_some_iff parameter input
      (.chain lay tree leafIdx otherChain currentStep)).2 ⟨digestBytes currentValue, rfl⟩
  cases hdecode : decodeProbe? parameter input with
  | none =>
      unfold verifierHashQuery
      rw [hdecode, hposition]
      apply preservesCoordinate_resolveVerifierInput parameter probe.coordinate
        (.position (.chain lay tree leafIdx otherChain currentStep)) input
      · unfold CoordinateChildrenAvoid
        by_cases hzero : currentStep.val = 0
        · simp only [hzero, if_pos]
          exact htargetNe.1
        · have hpositive : 0 < currentStep.val := Nat.pos_of_ne_zero hzero
          simp only [hzero]
          intro child hchild
          simp only [Position.children, dif_pos hpositive, List.mem_singleton] at hchild
          subst child
          exact htargetNe.2 _
      · exact htargetNe.2 _
  | some candidate =>
      have hcandidate := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
      have houtput := candidate.outputCoordinate_eq_position_of_matchesInput parameter input
        (.chain lay tree leafIdx otherChain currentStep) hcandidate
          ((decodePosition?_eq_some_iff parameter input
            (.chain lay tree leafIdx otherChain currentStep)).1 hposition)
      unfold verifierHashQuery
      rw [hdecode]
      exact (preservesCoordinate_probe probe.coordinate candidate).bind fun _ => by
        rw [houtput]
        apply preservesCoordinate_resolveVerifierInput parameter probe.coordinate
          (.position (.chain lay tree leafIdx otherChain currentStep)) input
        · unfold CoordinateChildrenAvoid
          by_cases hzero : currentStep.val = 0
          · simp only [hzero, if_pos]
            exact htargetNe.1
          · have hpositive : 0 < currentStep.val := Nat.pos_of_ne_zero hzero
            simp only [hzero]
            intro child hchild
            simp only [Position.children, dif_pos hpositive, List.mem_singleton] at hchild
            subst child
            exact htargetNe.2 _
        · exact htargetNe.2 _

theorem preservesCoordinate_verifierHashQuery_chain_of_layer_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (otherChain : ChainIndex) (otherStep : ChainStep) (value : Digest)
    (hne : otherLay ≠ lay) :
    PreservesCoordinate probe.coordinate
      (verifierHashQuery parameter
        (tweakableHashInput parameter
          (.chain otherLay otherTree otherLeaf otherChain otherStep) (digestBytes value))) := by
  let position := Position.chain otherLay otherTree otherLeaf otherChain otherStep
  apply preservesCoordinate_verifierHashQuery_at_position parameter probe.coordinate position _
    ⟨digestBytes value, rfl⟩ (by trivial)
  · unfold CoordinateChildrenAvoid position
    by_cases hzero : otherStep.val = 0
    · simp only [hzero, if_pos]
      exact probe.coordinate_ne_chainStart_of_matches_chain_layer_ne parameter lay tree leafIdx
        chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree otherLeaf
          otherChain hne
    · have hpositive : 0 < otherStep.val := Nat.pos_of_ne_zero hzero
      simp only [hzero]
      intro child hchild
      simp only [Position.children, dif_pos hpositive, List.mem_singleton] at hchild
      subst child
      exact probe.coordinate_ne_position_chain_of_matches_chain_layer_ne parameter lay tree
        leafIdx chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree
          otherLeaf otherChain _ hne
  · exact probe.coordinate_ne_position_chain_of_matches_chain_layer_ne parameter lay tree
      leafIdx chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree otherLeaf
        otherChain otherStep hne

theorem preservesCoordinate_verifierHashQuery_leaf_of_layer_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (payload : HashInput) (hne : otherLay ≠ lay) :
    PreservesCoordinate probe.coordinate
      (verifierHashQuery parameter
        (tweakableHashInput parameter (.leaf otherLay otherTree otherLeaf) payload)) := by
  let position := Position.leaf otherLay otherTree otherLeaf
  apply preservesCoordinate_verifierHashQuery_at_position parameter probe.coordinate position _
    ⟨payload, rfl⟩ (by trivial)
  · unfold CoordinateChildrenAvoid position
    intro child hchild
    simp only [Position.children, List.mem_ofFn] at hchild
    obtain ⟨otherChain, rfl⟩ := hchild
    exact probe.coordinate_ne_position_chain_of_matches_chain_layer_ne parameter lay tree leafIdx
      chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree otherLeaf
        otherChain Position.lastChainStep hne
  · exact probe.coordinate_ne_position_leaf_of_matches_chain_layer_ne parameter lay tree leafIdx
      chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree otherLeaf hne

theorem preservesCoordinate_verifierHashQuery_node_of_layer_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (otherLay : Layer) (otherTree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) (payload : HashInput) (hne : otherLay ≠ lay) :
    PreservesCoordinate probe.coordinate
      (verifierHashQuery parameter
        (tweakableHashInput parameter
          (.node otherLay otherTree (level.val + 1) nodeIdx.val) payload)) := by
  let position := Position.node otherLay otherTree level nodeIdx
  apply preservesCoordinate_verifierHashQuery_at_position parameter probe.coordinate position _
    ⟨payload, by simp [position, Position.domain]⟩ (by trivial)
  · unfold CoordinateChildrenAvoid position
    intro child hchild
    simp only [Position.children] at hchild
    split_ifs at hchild with hidx hlevel
    · rcases List.mem_pair.mp hchild with hleft | hright
      · subst child
        exact probe.coordinate_ne_position_node_of_matches_chain_layer_ne parameter lay tree
          leafIdx chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree _ _ hne
      · subst child
        exact probe.coordinate_ne_position_node_of_matches_chain_layer_ne parameter lay tree
          leafIdx chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree _ _ hne
    · rcases List.mem_pair.mp hchild with hleft | hright
      · subst child
        exact probe.coordinate_ne_position_leaf_of_matches_chain_layer_ne parameter lay tree
          leafIdx chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree _ hne
      · subst child
        exact probe.coordinate_ne_position_leaf_of_matches_chain_layer_ne parameter lay tree
          leafIdx chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree _ hne
    · simp at hchild
  · simpa only [position] using
      probe.coordinate_ne_position_node_of_matches_chain_layer_ne parameter lay tree leafIdx
        chainIdx targetStep (digestBytes targetValue) hmatches otherLay otherTree level nodeIdx hne

theorem verifierHashQuery_eq_splitHashQuery_of_stable
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    verifierHashQuery parameter input = splitHashQuery (.ordinary input) := by
  unfold verifierHashQuery
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

theorem preservesCoordinate_simulateQ_verifierHashImpl_tweakableHash_of_stable
    (parameter : PublicParameter) (coordinate : Coordinate)
    (domain : HashDomain) (payload : HashInput)
    (hstable : StableOrdinaryInput parameter
      (tweakableHashInput parameter domain payload)) :
    PreservesCoordinate coordinate
      (simulateQ (verifierHashImpl parameter)
        (tweakableHash parameter domain payload)) := by
  unfold tweakableHash oracleHash
  rw [simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query]
  change PreservesCoordinate coordinate
    (verifierHashQuery parameter (tweakableHashInput parameter domain payload) >>= fun output =>
      pure (truncateHash output))
  rw [verifierHashQuery_eq_splitHashQuery_of_stable parameter _ hstable]
  exact (preservesCoordinate_splitHashQuery coordinate _).bind fun _ =>
    preservesCoordinate_pure coordinate _

theorem preservesCoordinate_simulateQ_verifierHashImpl_chainWalk_of_chain_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx otherChain : ChainIndex) (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (hne : otherChain ≠ chainIdx) :
    ∀ start steps value,
      PreservesCoordinate probe.coordinate
        (simulateQ (verifierHashImpl parameter)
          (chainWalk parameter lay tree leafIdx otherChain start steps value)) := by
  intro start steps value
  induction steps with
  | zero =>
      rw [chainWalk, simulateQ_pure]
      exact preservesCoordinate_pure probe.coordinate value
  | succ steps ih =>
      rw [chainWalk, simulateQ_bind]
      exact ih.bind fun current => by
        split
        · exact (preservesCoordinate_verifierHashQuery_chain_of_ne parameter probe lay tree
            leafIdx chainIdx otherChain targetStep _ targetValue current hmatches hne).bind
              fun output => preservesCoordinate_pure probe.coordinate (truncateHash output)
        · exact preservesCoordinate_pure probe.coordinate 0

theorem preservesCoordinate_simulateQ_verifierHashImpl_recoverChain_of_chain_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx otherChain : ChainIndex) (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (hne : otherChain ≠ chainIdx) (digit : Digit) (value : Digest) :
    PreservesCoordinate probe.coordinate
      (simulateQ (verifierHashImpl parameter)
        (recoverChain parameter lay tree leafIdx otherChain digit value)) := by
  unfold recoverChain
  exact preservesCoordinate_simulateQ_verifierHashImpl_chainWalk_of_chain_ne parameter probe lay
    tree leafIdx chainIdx otherChain targetStep targetValue hmatches hne _ _ _

theorem preservesCoordinate_simulateQ_sequenceFin
    {spec : OracleSpec ι} (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (coordinate : Coordinate) {n : Nat} (computation : Fin n → OracleComp spec alpha)
    (hcomponent : ∀ index,
      PreservesCoordinate coordinate (simulateQ impl (computation index))) :
    PreservesCoordinate coordinate (simulateQ impl (sequenceFin computation)) := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure]
      exact preservesCoordinate_pure coordinate Fin.elim0
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind]
      exact (hcomponent 0).bind fun head => by
        rw [simulateQ_bind]
        exact (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail => by
            rw [simulateQ_pure]
            exact preservesCoordinate_pure coordinate
              (Fin.cases head tail : Fin (n + 1) → alpha)

theorem preservesCoordinate_simulateQ_verifierHashImpl_chainWalk_of_layer_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (otherChain : ChainIndex) (hne : otherLay ≠ lay) :
    ∀ start steps value,
      PreservesCoordinate probe.coordinate
        (simulateQ (verifierHashImpl parameter)
          (chainWalk parameter otherLay otherTree otherLeaf otherChain start steps value)) := by
  intro start steps value
  induction steps with
  | zero =>
      rw [chainWalk, simulateQ_pure]
      exact preservesCoordinate_pure probe.coordinate value
  | succ steps ih =>
      rw [chainWalk, simulateQ_bind]
      exact ih.bind fun current => by
        split
        · exact (preservesCoordinate_verifierHashQuery_chain_of_layer_ne parameter probe lay tree
            leafIdx chainIdx targetStep targetValue hmatches otherLay otherTree otherLeaf
              otherChain _ current hne).bind fun output =>
                preservesCoordinate_pure probe.coordinate (truncateHash output)
        · exact preservesCoordinate_pure probe.coordinate 0

theorem preservesCoordinate_simulateQ_verifierHashImpl_recoverChain_of_layer_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (otherChain : ChainIndex) (digit : Digit) (value : Digest) (hne : otherLay ≠ lay) :
    PreservesCoordinate probe.coordinate
      (simulateQ (verifierHashImpl parameter)
        (recoverChain parameter otherLay otherTree otherLeaf otherChain digit value)) := by
  unfold recoverChain
  exact preservesCoordinate_simulateQ_verifierHashImpl_chainWalk_of_layer_ne parameter probe lay
    tree leafIdx chainIdx targetStep targetValue hmatches otherLay otherTree otherLeaf otherChain
      hne _ _ _

theorem preservesCoordinate_simulateQ_verifierHashImpl_leafHash_of_layer_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (values : ChainIndex → Digest) (hne : otherLay ≠ lay) :
    PreservesCoordinate probe.coordinate
      (simulateQ (verifierHashImpl parameter)
        (leafHash parameter otherLay otherTree otherLeaf values)) := by
  unfold leafHash tweakableHash oracleHash
  rw [simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query]
  change PreservesCoordinate probe.coordinate
    (verifierHashQuery parameter
      (tweakableHashInput parameter (.leaf otherLay otherTree otherLeaf)
        (leafPayload values)) >>= fun output => pure (truncateHash output))
  exact (preservesCoordinate_verifierHashQuery_leaf_of_layer_ne parameter probe lay tree leafIdx
    chainIdx targetStep targetValue hmatches otherLay otherTree otherLeaf (leafPayload values)
      hne).bind fun _ => preservesCoordinate_pure probe.coordinate _

theorem preservesCoordinate_simulateQ_verifierHashImpl_encode
    (parameter : PublicParameter) (coordinate : Coordinate)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    PreservesCoordinate coordinate
      (simulateQ (verifierHashImpl parameter)
        (encode parameter lay tree leafIdx message counter)) := by
  rw [encode, simulateQ_bind]
  exact (preservesCoordinate_simulateQ_verifierHashImpl_tweakableHash_of_stable parameter
    coordinate (.encoding lay tree leafIdx) _
      (stableOrdinaryInput_tweakableHashInput parameter (.encoding lay tree leafIdx) _
        (by trivial) (by simp) (by simp) (by simp))).bind fun _ =>
          preservesCoordinate_pure coordinate _

theorem preservesCoordinate_simulateQ_verifierHashImpl_otsLeaf_of_layer_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (hne : otherLay ≠ lay) :
    PreservesCoordinate probe.coordinate
      (simulateQ (verifierHashImpl parameter)
        (otsLeaf parameter otherLay otherTree otherLeaf message counter values)) := by
  unfold otsLeaf
  rw [simulateQ_bind]
  exact (preservesCoordinate_simulateQ_verifierHashImpl_encode parameter probe.coordinate otherLay
    otherTree otherLeaf message counter).bind fun encoded =>
      match encoded with
      | none => preservesCoordinate_pure probe.coordinate none
      | some encoding => by
          rw [simulateQ_bind]
          exact (preservesCoordinate_simulateQ_sequenceFin (verifierHashImpl parameter)
            probe.coordinate (fun index => recoverChain parameter otherLay otherTree otherLeaf
              index (encoding index) (values index)) fun index =>
                preservesCoordinate_simulateQ_verifierHashImpl_recoverChain_of_layer_ne parameter
                  probe lay tree leafIdx chainIdx targetStep targetValue hmatches otherLay otherTree
                    otherLeaf index (encoding index) (values index) hne).bind fun endpoints => by
              rw [simulateQ_bind]
              exact (preservesCoordinate_simulateQ_verifierHashImpl_leafHash_of_layer_ne parameter
                probe lay tree leafIdx chainIdx targetStep targetValue hmatches otherLay otherTree
                  otherLeaf endpoints hne).bind fun value =>
                    preservesCoordinate_pure probe.coordinate (some value)

theorem preservesCoordinate_simulateQ_verifierHashImpl_treeFold_of_layer_ne
    (parameter : PublicParameter) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (targetStep : ChainStep) (targetValue : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx targetStep)
        (digestBytes targetValue)))
    (otherLay : Layer) (otherTree : TreeIndex) (otherLeaf : LeafIndex)
    (path : Nat → Digest) (hne : otherLay ≠ lay) :
    ∀ levels value, levels ≤ maxLayerHeight →
      PreservesCoordinate probe.coordinate
        (simulateQ (verifierHashImpl parameter)
          (treeFold parameter otherLay otherTree otherLeaf path levels value))
  | 0, value, _ => by
      rw [treeFold_zero_eq, simulateQ_pure]
      exact preservesCoordinate_pure probe.coordinate value
  | levels + 1, value, hlevels => by
      rw [treeFold_succ_eq, simulateQ_bind]
      exact (preservesCoordinate_simulateQ_verifierHashImpl_treeFold_of_layer_ne parameter probe
        lay tree leafIdx chainIdx targetStep targetValue hmatches otherLay otherTree otherLeaf path
          hne levels value (by omega)).bind fun current => by
            let level : Fin maxLayerHeight := ⟨levels, by omega⟩
            let nodeIdx : LeafIndex := ⟨otherLeaf.val / 2 ^ (levels + 1), by
              exact lt_of_le_of_lt (Nat.div_le_self _ _) otherLeaf.isLt⟩
            split <;>
              exact (preservesCoordinate_verifierHashQuery_node_of_layer_ne parameter probe lay
                tree leafIdx chainIdx targetStep targetValue hmatches otherLay otherTree level
                  nodeIdx _ hne).bind fun output =>
                    preservesCoordinate_pure probe.coordinate (truncateHash output)

theorem verifierHashQuery_pendingHit_of_cached_correct_probe_of_opaque
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (probe : Probe) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output cached : HashOutput)
    (hmatches : probe.MatchesInput parameter input)
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hvalue : state.values probe.coordinate = none)
    (hnotRevealed : probe.coordinate ∉ state.revealed)
    (hcached : cache (.ordinary input) = some cached)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter input).run cache))) :
    finalState.values probe.coordinate = none ∧
      finalState.hitAt probe.coordinate (table probe.coordinate) := by
  have hdecode : decodeProbe? parameter input = some probe :=
    (decodeProbe?_eq_some_iff parameter input probe).2 hmatches
  unfold verifierHashQuery at hresult
  rw [hdecode, StateT.run_bind, LazyRevealProbe.runRaw_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨probeRaw, hprobe, hresolve⟩ := hresult
  cases probeRaw with
  | stopped hit => simp at hresolve
  | done probeState probeRemaining probeResult =>
      rcases probeResult with ⟨probed, probeCache⟩
      change LazyRevealProbe.RawResult.done probeState probeRemaining
          (probed, probeCache) ∈ support
        (LazyRevealProbe.runRaw state fuel
          (LazyRevealProbe.probeQuery probe.coordinate probe.candidate >>= fun result =>
            pure (result, cache))) at hprobe
      rw [LazyRevealProbe.probeQuery,
        LazyRevealProbe.runRaw_probe_query_bind] at hprobe
      cases fuel with
      | zero => simp at hprobe
      | succ remainingFuel =>
          simp only at hprobe
          rw [if_neg hnotRevealed] at hprobe
          simp [LazyRevealProbe.runRaw] at hprobe
          rcases hprobe with ⟨rfl, rfl, rfl, rfl⟩
          unfold resolveVerifierInput at hresolve
          simp [hcached, LazyRevealProbe.runRaw] at hresolve
          rcases hresolve with ⟨rfl, rfl, rfl, rfl⟩
          constructor
          · simpa [LazyRevealProbe.State.addPending] using hvalue
          · rw [LazyRevealProbe.State.hitAt, ← hcandidate]
            exact LazyRevealProbe.State.pendingAt_addPending_self state probe.coordinate
              probe.candidate

theorem simulateQ_verifierHashImpl_tweakableHash_pendingHit_of_correct_probe_of_opaque
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (probe : Probe) (domain : HashDomain) (payload : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter domain payload))
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hvalue : state.values probe.coordinate = none)
    (hnotRevealed : probe.coordinate ∉ state.revealed)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter)
          (tweakableHash parameter domain payload)).run cache))) :
    finalState.values probe.coordinate = none ∧
      finalState.hitAt probe.coordinate (table probe.coordinate) := by
  cases hcached : cache (.ordinary (tweakableHashInput parameter domain payload)) with
  | none =>
      exact (simulateQ_verifierHashImpl_tweakableHash_not_done_of_fresh_correct_probe_of_opaque
        parameter table probe domain payload state finalState cache finalCache fuel remaining
          output hmatches hcandidate hvalue hnotRevealed hcached htable hresult).elim
  | some cached =>
      unfold tweakableHash oracleHash at hresult
      rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨queryRaw, hquery, hrest⟩ := hresult
      cases queryRaw with
      | stopped hit => simp at hrest
      | done queryState queryRemaining queryResult =>
          rcases queryResult with ⟨answer, queryCache⟩
          simp [LazyRevealProbe.runRaw] at hrest
          rcases hrest with ⟨rfl, rfl, rfl, rfl⟩
          have hquery' : LazyRevealProbe.RawResult.done finalState remaining
              (answer, finalCache) ∈ support
            (LazyRevealProbe.runRaw state fuel
              ((verifierHashQuery parameter
                (tweakableHashInput parameter domain payload)).run cache)) := by
            simpa only [HasQuery.instOfMonadLift_query, simulateQ_spec_query,
              verifierHashImpl] using hquery
          exact verifierHashQuery_pendingHit_of_cached_correct_probe_of_opaque parameter table
            probe (tweakableHashInput parameter domain payload) state finalState cache finalCache
              fuel remaining answer cached hmatches hcandidate hvalue hnotRevealed hcached hquery'

theorem simulateQ_verifierHashImpl_chainWalk_pendingHit_of_correct_probe_of_opaque
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (probe : Probe) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (initialValue : Digest)
    (hpositive : 0 < steps) (hrange : start + steps ≤ chainLength - 1)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨start, by omega⟩) (digestBytes initialValue)))
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hvalue : state.values probe.coordinate = none)
    (hnotRevealed : probe.coordinate ∉ state.revealed)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter)
          (chainWalk parameter lay tree leafIdx chainIdx start steps initialValue)).run cache))) :
    finalState.values probe.coordinate = none ∧
      finalState.hitAt probe.coordinate (table probe.coordinate) := by
  induction steps generalizing state finalState cache finalCache fuel remaining output with
  | zero => omega
  | succ steps ih =>
      cases steps with
      | zero =>
          have hstep : start < chainLength - 1 := by omega
          rw [chainWalk, chainWalk, pure_bind, Nat.add_zero, dif_pos hstep] at hresult
          exact simulateQ_verifierHashImpl_tweakableHash_pendingHit_of_correct_probe_of_opaque
            parameter table probe (.chain lay tree leafIdx chainIdx ⟨start, hstep⟩)
              (digestBytes initialValue) state finalState cache finalCache fuel remaining output
                (by simpa only using hmatches) hcandidate hvalue hnotRevealed htable hresult
      | succ previous =>
          rw [chainWalk, simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨prefixRaw, hprefix, hrest⟩ := hresult
          cases prefixRaw with
          | stopped hit => simp at hrest
          | done prefixState prefixRemaining prefixResult =>
              rcases prefixResult with ⟨prefixValue, prefixCache⟩
              simp only at hrest
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done _ prefixState
                finalState prefixRemaining remaining (output, finalCache) hrest
              have htablePrefix : ∀ coordinate cached,
                  prefixState.values coordinate = some cached → cached = table coordinate :=
                fun coordinate cached hcached =>
                  htable coordinate cached (hvaluesLE coordinate cached hcached)
              have hpending := ih (by omega) (by omega) state prefixState cache prefixCache fuel
                prefixRemaining prefixValue hmatches hvalue hnotRevealed htablePrefix hprefix
              exact LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done _
                probe.coordinate (table probe.coordinate) prefixState finalState prefixRemaining
                  remaining (output, finalCache) hpending.1 hpending.2
                    (htable probe.coordinate) hrest

theorem simulateQ_sequenceFin_bind_pendingHit_of_component
    {spec : OracleSpec ι} (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (coordinate : Coordinate) (table : Coordinate → HashOutput)
    {n : Nat} (computation : Fin n → OracleComp spec alpha) (target : Fin n)
    (hother : ∀ index, index ≠ target → PreservesCoordinate coordinate
      (simulateQ impl (computation index)))
    (htarget : ∀ state finalState cache finalCache fuel remaining value,
      state.values coordinate = none → coordinate ∉ state.revealed →
      (∀ other cached, finalState.values other = some cached → cached = table other) →
      LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel
          ((simulateQ impl (computation target)).run cache)) →
      finalState.values coordinate = none ∧
        finalState.hitAt coordinate (table coordinate))
    (next : (Fin n → alpha) → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : beta)
    (hvalue : state.values coordinate = none)
    (hnotRevealed : coordinate ∉ state.revealed)
    (htable : ∀ other cached, finalState.values other = some cached → cached = table other)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ impl (sequenceFin computation) >>= next).run cache))) :
    finalState.values coordinate = none ∧
      finalState.hitAt coordinate (table coordinate) := by
  induction n generalizing state finalState cache finalCache fuel remaining value with
  | zero => exact target.elim0
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind, bind_assoc, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨headRaw, hhead, hrest⟩ := hresult
      cases headRaw with
      | stopped hit => simp at hrest
      | done headState headRemaining headResult =>
          rcases headResult with ⟨head, headCache⟩
          cases target using Fin.cases with
          | zero =>
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done _ headState
                finalState headRemaining remaining (value, finalCache) hrest
              have htableHead : ∀ other cached,
                  headState.values other = some cached → cached = table other :=
                fun other cached hcached => htable other cached
                  (hvaluesLE other cached hcached)
              have hpending := htarget state headState cache headCache fuel headRemaining head
                hvalue hnotRevealed htableHead hhead
              exact LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done _ coordinate
                (table coordinate) headState finalState headRemaining remaining
                  (value, finalCache) hpending.1 hpending.2 (htable coordinate) hrest
          | succ target =>
              have hheadPreserves := hother 0 (by
                intro heq
                exact (Fin.succ_ne_zero target).symm heq)
              have hheadCoordinate := hheadPreserves state cache fuel headState headRemaining head
                headCache hhead
              have hheadValue : headState.values coordinate = none := by
                rw [hheadCoordinate.1, hvalue]
              have hheadNotRevealed : coordinate ∉ headState.revealed := by
                simpa [hheadCoordinate.2] using hnotRevealed
              apply ih (fun index => computation index.succ) target
                (fun index hne => hother index.succ (by
                  intro heq
                  exact hne (Fin.succ_inj.mp heq)))
                (by
                  intro initial terminal initialCache terminalCache initialFuel terminalFuel
                    result hinitialValue hinitialRevealed hterminalTable hrun
                  exact htarget initial terminal initialCache terminalCache initialFuel terminalFuel
                    result hinitialValue hinitialRevealed hterminalTable hrun)
                (fun tail => next (Fin.cases head tail)) headState finalState headCache finalCache
                  headRemaining remaining value hheadValue hheadNotRevealed htable
              simpa only [simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc] using hrest

set_option maxRecDepth 10000 in
theorem simulateQ_verifierHashImpl_otsLeaf_pendingHit_of_correct_probe
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (probe : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (codeword : Encoding) (chainIdx : ChainIndex)
    (hdigit : (codeword chainIdx).val < chainLength - 1)
    (hencode : evalWithAnswerFn f
      (encode parameter lay tree leafIdx message counter) = some codeword)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (result : Option Digest)
    (hmatches : probe.MatchesInput parameter
      (tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨(codeword chainIdx).val, hdigit⟩)
          (digestBytes (values chainIdx))))
    (hcandidate : probe.candidate = truncateHash (table probe.coordinate))
    (hvalue : state.values probe.coordinate = none)
    (hnotRevealed : probe.coordinate ∉ state.revealed)
    (hf : CacheAnswersAgreeOnRun (ordinaryQueryCache finalCache) f
      (encode parameter lay tree leafIdx message counter))
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (result, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter)
          (otsLeaf parameter lay tree leafIdx message counter values)).run cache))) :
    finalState.values probe.coordinate = none ∧
      finalState.hitAt probe.coordinate (table probe.coordinate) := by
  unfold otsLeaf at hresult
  rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨encodeRaw, hencodeRaw, hrest⟩ := hresult
  cases encodeRaw with
  | stopped hit => simp at hrest
  | done encodeState encodeRemaining encodeResult =>
      rcases encodeResult with ⟨encoded, encodeCache⟩
      have hfEncode : CacheAnswersAgreeOnRun (ordinaryQueryCache encodeCache) f
          (encode parameter lay tree leafIdx message counter) := by
        intro input hquery output hcached
        apply hf input hquery
        exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter input).simulateQ _
          encodeState encodeCache encodeRemaining finalState remaining result finalCache output
            hcached hrest
      have hencoded :=
        (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
        (encode parameter lay tree leafIdx message counter) state encodeState cache encodeCache
          fuel encodeRemaining encoded hfEncode hencodeRaw).1
      rw [hencode] at hencoded
      subst encoded
      simp only at hrest
      have hencodeCoordinate :=
        preservesCoordinate_simulateQ_verifierHashImpl_encode parameter probe.coordinate lay tree
          leafIdx message counter state cache fuel encodeState encodeRemaining (some codeword)
            encodeCache hencodeRaw
      have hencodeValue : encodeState.values probe.coordinate = none := by
        rw [hencodeCoordinate.1, hvalue]
      have hencodeNotRevealed : probe.coordinate ∉ encodeState.revealed := by
        simpa [hencodeCoordinate.2] using hnotRevealed
      let chains : ChainIndex → OracleComp HashSpec Digest := fun index =>
        recoverChain parameter lay tree leafIdx index (codeword index) (values index)
      apply simulateQ_sequenceFin_bind_pendingHit_of_component
        (verifierHashImpl parameter) probe.coordinate table chains chainIdx
        (fun index hne => by
          exact preservesCoordinate_simulateQ_verifierHashImpl_recoverChain_of_chain_ne
            parameter probe lay tree leafIdx chainIdx index
              ⟨(codeword chainIdx).val, hdigit⟩ (values chainIdx) hmatches hne
                (codeword index) (values index))
        (by
          intro initial terminal initialCache terminalCache initialFuel terminalFuel output
            hinitialValue hinitialRevealed hterminalTable hrun
          unfold chains recoverChain at hrun
          exact simulateQ_verifierHashImpl_chainWalk_pendingHit_of_correct_probe_of_opaque
            parameter table probe lay tree leafIdx chainIdx (codeword chainIdx).val
              (chainLength - 1 - (codeword chainIdx).val) (values chainIdx) (by omega)
                (by omega) initial terminal initialCache terminalCache initialFuel terminalFuel
                  output hmatches hcandidate hinitialValue hinitialRevealed hterminalTable hrun)
        (fun endpoints => do
          let value ← simulateQ (verifierHashImpl parameter)
            (leafHash parameter lay tree leafIdx endpoints)
          pure (some value)) encodeState finalState encodeCache finalCache encodeRemaining
            remaining result hencodeValue hencodeNotRevealed htable
      simpa only [chains, simulateQ_bind, simulateQ_pure] using hrest

theorem decodeProbe?_outputCoordinate_eq_position
    (parameter : PublicParameter) (input : HashInput) (probe : Probe)
    (position : Position) (hprobe : decodeProbe? parameter input = some probe)
    (hposition : decodePosition? parameter input = some position) :
    probe.outputCoordinate = .position position := by
  exact probe.outputCoordinate_eq_position_of_matchesInput parameter input position
    ((decodeProbe?_eq_some_iff parameter input probe).1 hprobe)
    ((decodePosition?_eq_some_iff parameter input position).1 hposition)

theorem verifierHashQuery_eq_resolveVerifierInput_of_decodeProbe_none
    (parameter : PublicParameter) (input : HashInput) (position : Position)
    (hprobe : decodeProbe? parameter input = none)
    (hposition : decodePosition? parameter input = some position)
    (hots : IsOtsPosition position) :
    verifierHashQuery parameter input =
      resolveVerifierInput parameter (.position position) input := by
  unfold verifierHashQuery
  rw [hprobe, hposition]
  cases position <;> simp [IsOtsPosition] at hots ⊢

set_option maxRecDepth 10000 in
theorem verifierHashQuery_returns_table_of_uncached
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (hots : IsOtsPosition position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (huncached : cache (.ordinary
      (tableInput parameter table (.position position))) = none)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter
          (tableInput parameter table (.position position))).run cache))) :
    output = table (.position position) ∧
      finalCache (.ordinary (tableInput parameter table (.position position))) = some output := by
  let input := tableInput parameter table (.position position)
  have hposition : decodePosition? parameter input = some position :=
    (decodePosition?_eq_some_iff parameter input position).2 ⟨tablePayload table position, rfl⟩
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      unfold verifierHashQuery at hresult
      rw [hprobe, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨probeRaw, hprobeRun, hrest⟩ := hresult
      cases probeRaw with
      | stopped hit => simp at hrest
      | done probeState probeRemaining probeResult =>
          rcases probeResult with ⟨probed, probeCache⟩
          have hprobeCache := splitCachePreserving_probe candidate state cache fuel probeState
            probeRemaining probed probeCache hprobeRun
          subst probeCache
          have houtputCoordinate := decodeProbe?_outputCoordinate_eq_position parameter input
            candidate position hprobe hposition
          rw [houtputCoordinate] at hrest
          exact resolveVerifierInput_returns_table_of_uncached parameter table position probeState
            finalState cache finalCache probeRemaining remaining output huncached htable hrest
  | none =>
      rw [verifierHashQuery_eq_resolveVerifierInput_of_decodeProbe_none parameter input position
        hprobe hposition hots] at hresult
      exact resolveVerifierInput_returns_table_of_uncached parameter table position state finalState
        cache finalCache fuel remaining output huncached htable hresult

theorem verifierHashQuery_output_eq_retainedCompletionAnswer_of_uncached
    (parameter : PublicParameter)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (input : HashInput)
    (state queryState completedState : LazyRevealProbe.State Coordinate)
    (cache queryCache rawCache : SplitHashCache) (fuel queryRemaining : Nat)
    (output : HashOutput)
    (huncached : cache (.ordinary input) = none)
    (hquery : LazyRevealProbe.RawResult.done queryState queryRemaining
        (output, queryCache) ∈ support
      (LazyRevealProbe.runRaw state fuel ((verifierHashQuery parameter input).run cache)))
    (hvalues : LazyRevealProbe.ValuesLE queryState completedState)
    (hcached : rawCache (.ordinary input) = some output) :
    output = retainedCompletionAnswer parameter completedState rawCache baseStarts input := by
  let table := retainedCompletionTable parameter completedState rawCache baseStarts
  have htableQuery : ∀ coordinate cached,
      queryState.values coordinate = some cached → cached = table coordinate := by
    intro coordinate cached hvalue
    exact (completedRealizedTable_of_value (splitFallback rawCache) parameter completedState
      baseStarts coordinate cached (hvalues coordinate cached hvalue)).symm
  rcases retainedCompletionAnswer_eq_fallback_or_exact_materialized parameter completedState
      rawCache baseStarts input with hfallback | ⟨position, hots, _hposition, hinput, _hvalue⟩
  · rw [hfallback]
    simp [splitFallback, hcached]
  · subst input
    have hreturns := verifierHashQuery_returns_table_of_uncached parameter table position hots
      state queryState cache queryCache fuel queryRemaining output huncached htableQuery hquery
    rw [retainedCompletionAnswer_realizes parameter completedState rawCache baseStarts position
      hots]
    exact hreturns.1

theorem ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_splitHashQuery_ordinary
    (input : HashInput) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((splitHashQuery (.ordinary input)).run cache))) :
    ordinaryQueryCache finalCache = (ordinaryQueryCache cache).cacheQuery input output := by
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some cached =>
      rw [hlookup] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      funext other
      by_cases heq : other = input
      · subst other
        simp [QueryCache.cacheQuery, ordinaryQueryCache, hlookup]
      · simp [QueryCache.cacheQuery, heq]
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      rw [LazyRevealProbe.hashOutputQuery,
        LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hdone⟩ := hresult
      simp [LazyRevealProbe.runRaw] at hdone
      rcases hdone with ⟨rfl, rfl, rfl, rfl⟩
      exact ordinaryQueryCache_update cache input output

def OrdinaryCachePreserving
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    ordinaryQueryCache finalCache = ordinaryQueryCache cache

def OrdinaryCacheQuerying (input : HashInput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput) : Prop :=
  ∀ state cache fuel finalState remaining output finalCache,
    LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    ordinaryQueryCache finalCache = (ordinaryQueryCache cache).cacheQuery input output

theorem OrdinaryCachePreserving.of_splitCachePreserving
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hpreserves : SplitCachePreserving computation) :
    OrdinaryCachePreserving computation := by
  intro state cache fuel finalState remaining value finalCache hresult
  rw [hpreserves state cache fuel finalState remaining value finalCache hresult]

theorem RawReadOnly.ordinaryCachePreserving
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hreadonly : RawReadOnly computation) : OrdinaryCachePreserving computation := by
  intro state cache fuel finalState remaining value finalCache hresult
  rw [(hreadonly state cache fuel finalState remaining value finalCache hresult).2.2]

theorem OrdinaryCachePreserving.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : OrdinaryCachePreserving left)
    (hnext : ∀ value, OrdinaryCachePreserving (next value)) :
    OrdinaryCachePreserving (left >>= next) := by
  intro state cache fuel finalState remaining value finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      exact (hnext middleValue middleState middleCache middleRemaining finalState remaining value
        finalCache hrest).trans
          (hleft state cache fuel middleState middleRemaining middleValue middleCache hraw)

def PreservesOrdinaryAbsence (input : HashInput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    cache (.ordinary input) = none →
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    finalCache (.ordinary input) = none

theorem PreservesOrdinaryAbsence.pure (input : HashInput) (value : alpha) :
    PreservesOrdinaryAbsence input
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hnone hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hnone

theorem PreservesOrdinaryAbsence.bind
    {input : HashInput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesOrdinaryAbsence input left)
    (hnext : ∀ value, PreservesOrdinaryAbsence input (next value)) :
    PreservesOrdinaryAbsence input (left >>= next) := by
  intro state cache fuel finalState remaining value finalCache hnone hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      exact hnext middleValue middleState middleCache middleRemaining finalState remaining value
        finalCache (hleft state cache fuel middleState middleRemaining middleValue middleCache
          hnone hraw) hrest

theorem PreservesOrdinaryAbsence.sequenceFin
    {input : HashInput} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, PreservesOrdinaryAbsence input (computation index)) :
    PreservesOrdinaryAbsence input (sequenceFin computation) := by
  induction n with
  | zero => exact PreservesOrdinaryAbsence.pure input Fin.elim0
  | succ n ih =>
      rw [SphincsSecurity.Concrete.sequenceFin]
      exact (hcomputation 0).bind fun _ =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun _ =>
            PreservesOrdinaryAbsence.pure input _

theorem OrdinaryCachePreserving.preservesAbsence
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hpreserves : OrdinaryCachePreserving computation) (input : HashInput) :
    PreservesOrdinaryAbsence input computation := by
  intro state cache fuel finalState remaining value finalCache hnone hresult
  change ordinaryQueryCache finalCache input = none
  change ordinaryQueryCache cache input = none at hnone
  rw [hpreserves state cache fuel finalState remaining value finalCache hresult]
  exact hnone

theorem preservesOrdinaryAbsence_simulateQ_ordinaryHashImpl_of_stable
    (parameter : PublicParameter) (input : HashInput)
    (hnotStable : ¬StableOrdinaryInput parameter input)
    (computation : OracleComp HashSpec alpha)
    (hstable : ∀ f : QueryImpl HashSpec Id, QueriesStable parameter f computation) :
    PreservesOrdinaryAbsence input (simulateQ ordinaryHashImpl computation) := by
  intro state cache fuel finalState remaining value finalCache hnone hresult
  have hprojection := mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state
    finalState cache finalCache fuel remaining value hresult
  obtain ⟨_, f, hf, _, _⟩ := exists_answerFn_replay_of_mem_support computation
    (ordinaryQueryCache cache) value (ordinaryQueryCache finalCache) hprojection.2.2
  have hnot : input ∉ queriedInputs f computation := by
    intro hinput
    exact hnotStable (hstable f input hinput)
  exact cache_eq_none_of_not_mem_queriedInputs computation (ordinaryQueryCache cache) value
    (ordinaryQueryCache finalCache) hprojection.2.2 f hf input hnone hnot

theorem OrdinaryCachePreserving.bind_querying
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput}
    {input : HashInput}
    (hleft : OrdinaryCachePreserving left)
    (hnext : ∀ value, OrdinaryCacheQuerying input (next value)) :
    OrdinaryCacheQuerying input (left >>= next) := by
  intro state cache fuel finalState remaining output finalCache hresult
  change LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      rw [hnext middleValue middleState middleCache middleRemaining finalState remaining output
        finalCache hrest,
        hleft state cache fuel middleState middleRemaining middleValue middleCache hraw]

theorem ordinaryCachePreserving_revealCoordinateOutput (coordinate : Coordinate) :
    OrdinaryCachePreserving (revealCoordinateOutput coordinate) := by
  intro state cache fuel finalState remaining value finalCache hresult
  rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
    LazyRevealProbe.runRaw_reveal_query_bind] at hresult
  cases hvalue : state.values coordinate with
  | some existing =>
      rw [hvalue] at hresult
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ordinaryQueryCache_update_hidden cache coordinate value
  | none =>
      rw [hvalue, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hsampled⟩ := hresult
      by_cases hhit : state.hitAt coordinate sampled
      · rw [if_pos hhit] at hsampled
        simp at hsampled
      · rw [if_neg hhit] at hsampled
        simp [LazyRevealProbe.runRaw] at hsampled
        rcases hsampled with ⟨rfl, rfl, rfl, rfl⟩
        exact ordinaryQueryCache_update_hidden cache coordinate value

theorem ordinaryCachePreserving_revealCoordinate (coordinate : Coordinate) :
    OrdinaryCachePreserving (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (ordinaryCachePreserving_revealCoordinateOutput coordinate).bind fun _ =>
    OrdinaryCachePreserving.of_splitCachePreserving (SplitCachePreserving.pure _)

theorem ordinaryCachePreserving_revealPositionValues (positions : List Position) :
    OrdinaryCachePreserving (revealPositionValues positions) := by
  induction positions with
  | nil => exact OrdinaryCachePreserving.of_splitCachePreserving (SplitCachePreserving.pure [])
  | cons position remaining ih =>
      rw [revealPositionValues]
      exact (ordinaryCachePreserving_revealCoordinate (.position position)).bind fun _ =>
        ih.bind fun _ => OrdinaryCachePreserving.of_splitCachePreserving
          (SplitCachePreserving.pure _)

theorem ordinaryCachePreserving_revealTableInputChildren (coordinate : Coordinate) :
    OrdinaryCachePreserving (revealTableInputChildren coordinate) := by
  cases coordinate with
  | chainStart =>
      exact OrdinaryCachePreserving.of_splitCachePreserving (SplitCachePreserving.pure ())
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hzero : step.val = 0
          · simp only [revealTableInputChildren, hzero, ↓reduceIte]
            exact (ordinaryCachePreserving_revealCoordinate
              (.chainStart lay tree leafIdx chainIdx)).bind fun _ =>
                OrdinaryCachePreserving.of_splitCachePreserving (SplitCachePreserving.pure ())
          · simp only [revealTableInputChildren, hzero, ↓reduceIte]
            exact (ordinaryCachePreserving_revealPositionValues _).bind fun _ =>
              OrdinaryCachePreserving.of_splitCachePreserving (SplitCachePreserving.pure ())
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [revealTableInputChildren]
          exact (ordinaryCachePreserving_revealPositionValues _).bind fun _ =>
            OrdinaryCachePreserving.of_splitCachePreserving (SplitCachePreserving.pure ())

theorem OrdinaryCachePreserving.sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomputation : ∀ index, OrdinaryCachePreserving (computation index)) :
    OrdinaryCachePreserving (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [SphincsSecurity.Concrete.sequenceFin]
      exact OrdinaryCachePreserving.of_splitCachePreserving
        (SplitCachePreserving.pure Fin.elim0)
  | succ n ih =>
      rw [SphincsSecurity.Concrete.sequenceFin]
      exact (hcomputation 0).bind fun _ =>
        (ih (fun index => computation index.succ)
          (fun index => hcomputation index.succ)).bind fun _ =>
            OrdinaryCachePreserving.of_splitCachePreserving (SplitCachePreserving.pure _)

theorem ordinaryCachePreserving_simulateQ_splitUniformImpl
    (computation : ProbComp alpha) :
    OrdinaryCachePreserving (simulateQ splitUniformImpl computation) := by
  intro state cache fuel finalState remaining value finalCache hresult
  exact congrArg ordinaryQueryCache
    (mem_runRaw_simulateQ_splitUniformImpl_projects computation state finalState cache
      finalCache fuel remaining value hresult).2.2.1

theorem ordinaryCachePreserving_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    OrdinaryCachePreserving (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (OrdinaryCachePreserving.of_splitCachePreserving
        (splitCachePreserving_ensureTreeNode lay tree 0 nodeIdx)).bind fun _ =>
          ordinaryCachePreserving_revealCoordinate _
  | succ current =>
      rw [maskedTreeNode]
      exact (OrdinaryCachePreserving.of_splitCachePreserving
        (splitCachePreserving_ensureTreeNode lay tree (current + 1) nodeIdx)).bind fun _ => by
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact ordinaryCachePreserving_revealCoordinate _
          · rw [dif_neg hlevel]
            exact OrdinaryCachePreserving.of_splitCachePreserving
              (SplitCachePreserving.pure 0)

theorem ordinaryCachePreserving_maskedTreeRoot (lay : Layer) (tree : TreeIndex) :
    OrdinaryCachePreserving (maskedTreeRoot lay tree) :=
  ordinaryCachePreserving_maskedTreeNode lay tree (layerHeight lay) 0

theorem ordinaryCachePreserving_revealPublishedCoordinate (coordinate : Coordinate) :
    OrdinaryCachePreserving (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (ordinaryCachePreserving_revealCoordinate coordinate).bind fun _ =>
    (OrdinaryCachePreserving.of_splitCachePreserving
      (splitCachePreserving_publishCoordinate coordinate)).bind fun _ =>
        OrdinaryCachePreserving.of_splitCachePreserving (SplitCachePreserving.pure _)

theorem preservesOrdinaryAbsence_maskedLayerMessage
    (parameter : PublicParameter) (input : HashInput)
    (hnotStable : ¬StableOrdinaryInput parameter input)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    PreservesOrdinaryAbsence input (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact (ordinaryCachePreserving_maskedTreeRoot _ _).preservesAbsence input
  · exact preservesOrdinaryAbsence_simulateQ_ordinaryHashImpl_of_stable parameter input
      hnotStable _ (fun f => queriesStable_ftsKey f parameter index (ftsSecret index))

theorem preservesOrdinaryAbsence_maskedOtsSignFrom
    (parameter : PublicParameter) (input : HashInput)
    (hnotStable : ¬StableOrdinaryInput parameter input)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      PreservesOrdinaryAbsence input
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => PreservesOrdinaryAbsence.pure input none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (preservesOrdinaryAbsence_simulateQ_ordinaryHashImpl_of_stable parameter input
        hnotStable _ (fun f => queriesStable_encode f parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded =>
            match encoded with
            | none => preservesOrdinaryAbsence_maskedOtsSignFrom parameter input hnotStable
                lay tree leafIdx message attempts (counter + 1)
            | some encoding =>
                ((OrdinaryCachePreserving.of_splitCachePreserving
                  (splitCachePreserving_sequenceFin _ fun chainIdx =>
                    splitCachePreserving_ensureChainPrefix lay tree leafIdx chainIdx
                      (encoding chainIdx))).bind fun _ =>
                        OrdinaryCachePreserving.of_splitCachePreserving
                          (SplitCachePreserving.pure _)).preservesAbsence input

theorem preservesOrdinaryAbsence_maskedOtsSign
    (parameter : PublicParameter) (input : HashInput)
    (hnotStable : ¬StableOrdinaryInput parameter input)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    PreservesOrdinaryAbsence input
      (maskedOtsSign parameter lay tree leafIdx message) :=
  preservesOrdinaryAbsence_maskedOtsSignFrom parameter input hnotStable lay tree leafIdx message
    encodingAttemptLimit 0

theorem preservesOrdinaryAbsence_maskedSignLayer
    (parameter : PublicParameter) (input : HashInput)
    (hnotStable : ¬StableOrdinaryInput parameter input)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    PreservesOrdinaryAbsence input (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (preservesOrdinaryAbsence_maskedLayerMessage parameter input hnotStable ftsSecret index
    lay).bind fun message =>
      (preservesOrdinaryAbsence_maskedOtsSign parameter input hnotStable lay
        (treeIndexAt index lay) (leafIndexAt index lay) message).bind fun result =>
          match result with
          | none => PreservesOrdinaryAbsence.pure input none
          | some _ =>
              ((OrdinaryCachePreserving.of_splitCachePreserving
                (splitCachePreserving_ensureTreePath lay (treeIndexAt index lay)
                  (leafIndexAt index lay))).bind fun _ =>
                    OrdinaryCachePreserving.of_splitCachePreserving
                      (SplitCachePreserving.pure _)).preservesAbsence input

theorem ordinaryCachePreserving_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    OrdinaryCachePreserving (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (OrdinaryCachePreserving.sequenceFin _ fun chainIdx =>
    ordinaryCachePreserving_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))).bind fun _ =>
          (OrdinaryCachePreserving.sequenceFin _ fun level => by
            split
            · cases hlevelValue : level.val with
              | zero => exact ordinaryCachePreserving_revealPublishedCoordinate _
              | succ current =>
                  rw [show current + 1 = Nat.succ current by omega]
                  change OrdinaryCachePreserving
                    (if hlevel : current < maxLayerHeight then
                      revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                        ⟨current, hlevel⟩ (leafOfNat
                          (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                    else pure 0)
                  by_cases hlevel : current < maxLayerHeight
                  · rw [dif_pos hlevel]
                    exact ordinaryCachePreserving_revealPublishedCoordinate _
                  · rw [dif_neg hlevel]
                    exact OrdinaryCachePreserving.of_splitCachePreserving
                      (SplitCachePreserving.pure 0)
            · exact OrdinaryCachePreserving.of_splitCachePreserving
                (SplitCachePreserving.pure 0)).bind fun _ =>
                  OrdinaryCachePreserving.of_splitCachePreserving
                    (SplitCachePreserving.pure _)

theorem preservesOrdinaryAbsence_ordinarySignDigestLoop
    (secretKey : SecretKey) (input : HashInput)
    (hnotStable : ¬StableOrdinaryInput secretKey.parameter input)
    (attempts : Nat) (message : Message) :
    PreservesOrdinaryAbsence input
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message)) := by
  induction attempts with
  | zero =>
      rw [signDigestLoop, simulateQ_pure]
      exact PreservesOrdinaryAbsence.pure input none
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind]
      have hrandomness : PreservesOrdinaryAbsence input
          (simulateQ ordinaryRomImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left]
        exact (ordinaryCachePreserving_simulateQ_splitUniformImpl sampleRandomness).preservesAbsence
          input
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind]
        have hattempt : PreservesOrdinaryAbsence input
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right]
          exact preservesOrdinaryAbsence_simulateQ_ordinaryHashImpl_of_stable
            secretKey.parameter input hnotStable _
              (fun f => queriesStable_signAttempt f secretKey message randomness)
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none => exact ih
          | some selected => exact PreservesOrdinaryAbsence.pure input _

theorem preservesOrdinaryAbsence_maskedSignAfterDigest
    (parameter : PublicParameter) (input : HashInput)
    (hnotStable : ¬StableOrdinaryInput parameter input)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    PreservesOrdinaryAbsence input
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (preservesOrdinaryAbsence_simulateQ_ordinaryHashImpl_of_stable parameter input
    hnotStable _ (fun f => queriesStable_ftsOpen f parameter index leaves
      (ftsSecret index))).bind fun _ =>
        (PreservesOrdinaryAbsence.sequenceFin _ fun lay =>
          preservesOrdinaryAbsence_maskedSignLayer parameter input hnotStable ftsSecret index
            lay).bind fun layers =>
              match hparts : traverseOption layers with
              | none => PreservesOrdinaryAbsence.pure input none
              | some parts =>
                  ((OrdinaryCachePreserving.sequenceFin _ fun lay =>
                    ordinaryCachePreserving_revealLayerValues index lay
                      (parts lay).2).bind fun _ =>
                        OrdinaryCachePreserving.of_splitCachePreserving
                          (SplitCachePreserving.pure _)).preservesAbsence input

theorem preservesOrdinaryAbsence_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (hnotStable : ¬StableOrdinaryInput parameter input)
    (message : Message) :
    PreservesOrdinaryAbsence input (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  exact (preservesOrdinaryAbsence_ordinarySignDigestLoop
    (⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ : SecretKey) input hnotStable
      digestAttemptLimit message).bind fun selected =>
      match selected with
      | none => PreservesOrdinaryAbsence.pure input none
      | some data => preservesOrdinaryAbsence_maskedSignAfterDigest parameter input hnotStable
          ftsSecret data.1 data.2.1 data.2.2

theorem preservesOrdinaryAbsence_maskedSigningImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (hnotStable : ¬StableOrdinaryInput parameter input) :
    ∀ message, PreservesOrdinaryAbsence input
      (maskedSigningImpl parameter root ftsSecret message) :=
  fun message => preservesOrdinaryAbsence_maskedSign parameter root ftsSecret input hnotStable
    message

theorem preservesPublishedValues_maskedLayerMessage
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    PreservesPublishedValues (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact preservesPublishedValues_maskedTreeRoot _ _
  · exact preservesPublishedValues_simulateQ_ordinaryHashImpl _

theorem preservesPublishedValues_maskedOtsSignFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      PreservesPublishedValues
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => PreservesPublishedValues.pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (preservesPublishedValues_simulateQ_ordinaryHashImpl _).bind fun encoded =>
        match encoded with
        | none => preservesPublishedValues_maskedOtsSignFrom parameter lay tree leafIdx message
            attempts (counter + 1)
        | some encoding =>
            (PreservesPublishedValues.sequenceFin _ fun chainIdx =>
              preservesPublishedValues_ensureChainPrefix lay tree leafIdx chainIdx
                (encoding chainIdx)).bind fun _ => PreservesPublishedValues.pure _

theorem preservesPublishedValues_maskedOtsSign
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    PreservesPublishedValues (maskedOtsSign parameter lay tree leafIdx message) :=
  preservesPublishedValues_maskedOtsSignFrom parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem preservesPublishedValues_maskedSignLayer
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    PreservesPublishedValues (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (preservesPublishedValues_maskedLayerMessage parameter ftsSecret index lay).bind
    fun message =>
      (preservesPublishedValues_maskedOtsSign parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message).bind fun result =>
          match result with
          | none => PreservesPublishedValues.pure none
          | some _ => (preservesPublishedValues_ensureTreePath lay (treeIndexAt index lay)
              (leafIndexAt index lay)).bind fun _ => PreservesPublishedValues.pure _

theorem preservesPublishedValues_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    PreservesPublishedValues (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (PreservesPublishedValues.sequenceFin _ fun chainIdx =>
    preservesPublishedValues_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))).bind fun _ =>
          (PreservesPublishedValues.sequenceFin _ fun level => by
            split
            · cases hlevelValue : level.val with
              | zero => exact preservesPublishedValues_revealPublishedCoordinate _
              | succ current =>
                  rw [show current + 1 = Nat.succ current by omega]
                  change PreservesPublishedValues
                    (if hlevel : current < maxLayerHeight then
                      revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                        ⟨current, hlevel⟩ (leafOfNat
                          (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                    else pure 0)
                  by_cases hlevel : current < maxLayerHeight
                  · rw [dif_pos hlevel]
                    exact preservesPublishedValues_revealPublishedCoordinate _
                  · rw [dif_neg hlevel]
                    exact PreservesPublishedValues.pure 0
            · exact PreservesPublishedValues.pure 0).bind fun _ =>
                  PreservesPublishedValues.pure _

theorem preservesPublishedValues_ordinarySignDigestLoop
    (secretKey : SecretKey) (attempts : Nat) (message : Message) :
    PreservesPublishedValues
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message)) := by
  induction attempts with
  | zero =>
      rw [signDigestLoop, simulateQ_pure]
      exact PreservesPublishedValues.pure none
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind]
      have hrandomness : PreservesPublishedValues
          (simulateQ ordinaryRomImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left]
        exact preservesPublishedValues_simulateQ_splitUniformImpl sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind]
        have hattempt : PreservesPublishedValues
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right]
          exact preservesPublishedValues_simulateQ_ordinaryHashImpl _
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none => exact ih
          | some selected => exact PreservesPublishedValues.pure _

theorem preservesPublishedValues_maskedSignAfterDigest
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    PreservesPublishedValues
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (preservesPublishedValues_simulateQ_ordinaryHashImpl _).bind fun _ =>
    (PreservesPublishedValues.sequenceFin _ fun lay =>
      preservesPublishedValues_maskedSignLayer parameter ftsSecret index lay).bind fun layers =>
        match traverseOption layers with
        | none => PreservesPublishedValues.pure none
        | some parts => (PreservesPublishedValues.sequenceFin _ fun lay =>
            preservesPublishedValues_revealLayerValues index lay (parts lay).2).bind fun _ =>
              PreservesPublishedValues.pure _

theorem preservesPublishedValues_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    PreservesPublishedValues (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  exact (preservesPublishedValues_ordinarySignDigestLoop
    (⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ : SecretKey) digestAttemptLimit
      message).bind fun selected => match selected with
        | none => PreservesPublishedValues.pure none
        | some data => preservesPublishedValues_maskedSignAfterDigest parameter ftsSecret
            data.1 data.2.1 data.2.2

theorem preservesPublishedValues_maskedSigningImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ∀ message, PreservesPublishedValues (maskedSigningImpl parameter root ftsSecret message) :=
  fun message => preservesPublishedValues_maskedSign parameter root ftsSecret message

theorem preservesPublishedValuesImpl_splitUniformImpl :
    PreservesPublishedValuesImpl splitUniformImpl := by
  intro n
  simpa [splitUniformImpl] using preservesPublishedValues_simulateQ_splitUniformImpl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))

theorem preservesPublishedValuesImpl_probingHashImpl (parameter : PublicParameter) :
    PreservesPublishedValuesImpl (probingHashImpl parameter) :=
  fun input => preservesPublishedValues_probingHashQuery parameter input

theorem preservesPublishedValuesImpl_probingRomImpl (parameter : PublicParameter) :
    PreservesPublishedValuesImpl (probingRomImpl parameter) := by
  intro query
  cases query with
  | inl query => exact preservesPublishedValuesImpl_splitUniformImpl query
  | inr query => exact preservesPublishedValuesImpl_probingHashImpl parameter query

theorem preservesPublishedValuesImpl_verifierHashImpl (parameter : PublicParameter) :
    PreservesPublishedValuesImpl (verifierHashImpl parameter) :=
  fun input => preservesPublishedValues_verifierHashQuery parameter input

theorem preservesPublishedValuesImpl_verifierRomImpl (parameter : PublicParameter) :
    PreservesPublishedValuesImpl (verifierRomImpl parameter) := by
  intro query
  cases query with
  | inl query => exact preservesPublishedValuesImpl_splitUniformImpl query
  | inr query => exact preservesPublishedValuesImpl_verifierHashImpl parameter query

theorem preservesPublishedValuesImpl_maskedSigningImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    PreservesPublishedValuesImpl (maskedSigningImpl parameter root ftsSecret) :=
  preservesPublishedValues_maskedSigningImpl parameter root ftsSecret

theorem preservesPublishedValuesImpl_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    PreservesPublishedValuesImpl (maskedExpandedAdversaryImpl parameter root ftsSecret) := by
  intro query
  cases query with
  | inl query => exact preservesPublishedValuesImpl_probingRomImpl parameter query
  | inr query => exact preservesPublishedValuesImpl_maskedSigningImpl parameter root ftsSecret query

theorem publishedValues_of_mem_runRaw_maskedRetainedGameAfterFtsSecrets
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel remaining : Nat) (rawState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache))) :
    PublishedValues rawState := by
  let rootCoordinate : Coordinate := .position (.node topLayer rootTree
    ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0)
  unfold maskedRetainedGameAfterFtsSecrets at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨rootRaw, hroot, hafterRoot⟩ := hresult
  cases rootRaw with
  | stopped hit => simp at hafterRoot
  | done rootState rootRemaining rootResult =>
      rcases rootResult with ⟨sampledRoot, rootCache⟩
      simp only at hafterRoot
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterRoot
      obtain ⟨publishRaw, hpublish, hafterPublish⟩ := hafterRoot
      cases publishRaw with
      | stopped hit => simp at hafterPublish
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          simp only at hafterPublish
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterPublish
          obtain ⟨restRaw, hrest, hfinish⟩ := hafterPublish
          cases restRaw with
          | stopped hit => simp at hfinish
          | done restState restRemaining restResult =>
              rcases restResult with ⟨⟨prefixForgery, prefixLog⟩, restCache⟩
              simp only at hfinish
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hfinish
              obtain ⟨verifyRaw, hverify, hreturn⟩ := hfinish
              cases verifyRaw with
              | stopped hit => simp at hreturn
              | done verifyState verifyRemaining verifyResult =>
                  rcases verifyResult with ⟨prefixVerified, verifyCache⟩
                  simp [LazyRevealProbe.runRaw] at hreturn
                  rcases hreturn with ⟨rfl, rfl, _, rfl⟩
                  have hpublishedEmpty : PublishedValues
                      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) := by
                    intro coordinate hcoordinate
                    simp [LazyRevealProbe.State.empty] at hcoordinate
                  have hpublishedRoot := preservesPublishedValues_maskedTreeRoot topLayer rootTree
                    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
                      emptySplitHashCache fuel rootState rootRemaining sampledRoot rootCache
                        hpublishedEmpty hroot
                  obtain ⟨rootOutput, _, hrootValue, _⟩ :=
                    mem_runRaw_maskedTreeRoot_hidden topLayer rootTree
                      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) rootState
                        emptySplitHashCache rootCache fuel rootRemaining sampledRoot hroot
                  have hrootCoordinate :
                      maskedTreeRootCoordinate topLayer rootTree = rootCoordinate := by
                    simp [maskedTreeRootCoordinate, maskedTreeRootLevel, rootCoordinate,
                      layerHeight, topLayer, maxLayerHeight]
                  have hrootValue' : rootState.values rootCoordinate ≠ none := by
                    rw [← hrootCoordinate, hrootValue]
                    simp
                  have hpublishedPublish := publishedValues_of_mem_runRaw_publishCoordinate
                    rootCoordinate rootState publishState rootCache publishCache rootRemaining
                      publishRemaining publishedUnit hpublishedRoot hrootValue'
                        (by simpa [rootCoordinate] using hpublish)
                  have hpublishedRest :=
                    (preservesPublishedValuesImpl_maskedExpandedAdversaryImpl parameter sampledRoot
                      ftsSecret).simulateQ
                        (signingTraceComputation (adversary.main ⟨sampledRoot, parameter⟩))
                          publishState publishCache publishRemaining restState restRemaining
                            (prefixForgery, prefixLog) restCache hpublishedPublish hrest
                  exact (preservesPublishedValuesImpl_verifierRomImpl parameter).simulateQ
                    (scheme.verify ⟨sampledRoot, parameter⟩ prefixForgery.message
                      prefixForgery.signature) restState restCache restRemaining rawState
                        remaining prefixVerified rawCache hpublishedRest hverify

theorem ordinaryCacheQuerying_modifyOrdinary_pure (input : HashInput) (answer : HashOutput) :
    OrdinaryCacheQuerying input (do
      modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some answer)
      pure answer) := by
  intro state cache fuel finalState remaining output finalCache hresult
  simp [StateT.run_modify, LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact ordinaryQueryCache_update cache input output

theorem ordinaryCacheQuerying_splitHashQuery (input : HashInput) :
    OrdinaryCacheQuerying input (splitHashQuery (.ordinary input)) := by
  intro state cache fuel finalState remaining output finalCache hresult
  exact ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_splitHashQuery_ordinary input state
    finalState cache finalCache fuel remaining output hresult

theorem ordinaryCacheQuerying_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    OrdinaryCacheQuerying input (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply (rawReadOnly_peekTableInput parameter coordinate).ordinaryCachePreserving.bind_querying
  intro knownInput
  cases knownInput with
  | none => exact ordinaryCacheQuerying_splitHashQuery input
  | some knownInput =>
      simp only
      by_cases hexact : knownInput = input
      · rw [if_pos hexact]
        exact (ordinaryCachePreserving_revealCoordinateOutput coordinate).bind_querying fun answer =>
          (OrdinaryCachePreserving.of_splitCachePreserving
            (splitCachePreserving_publishCoordinate coordinate)).bind_querying fun _ =>
              ordinaryCacheQuerying_modifyOrdinary_pure input answer
      · rw [if_neg hexact]
        exact ordinaryCacheQuerying_splitHashQuery input

theorem ordinaryCachePreserving_prepareLeafInputProbe
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    OrdinaryCachePreserving (prepareLeafInputProbe input candidate lay tree leafIdx) :=
  OrdinaryCachePreserving.of_splitCachePreserving
    (splitCachePreserving_prepareLeafInputProbe input candidate lay tree leafIdx)

theorem ordinaryCacheQuerying_probingHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    OrdinaryCacheQuerying input (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases decodePosition? parameter input with
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (ordinaryCachePreserving_prepareLeafInputProbe input candidate lay tree
                leafIdx).bind_querying fun _ => ordinaryCacheQuerying_resolveKnownInput parameter
                  candidate.outputCoordinate input
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact (OrdinaryCachePreserving.of_splitCachePreserving
                (splitCachePreserving_probe candidate)).bind_querying fun _ =>
                  ordinaryCacheQuerying_resolveKnownInput parameter
                    candidate.outputCoordinate input
      | none => exact (OrdinaryCachePreserving.of_splitCachePreserving
          (splitCachePreserving_probe candidate)).bind_querying fun _ =>
            ordinaryCacheQuerying_resolveKnownInput parameter candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact ordinaryCacheQuerying_splitHashQuery input
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact ordinaryCacheQuerying_resolveKnownInput parameter
                (.position (.chain lay tree leafIdx chainIdx step)) input
          | leaf lay tree leafIdx =>
              exact ordinaryCacheQuerying_resolveKnownInput parameter
                (.position (.leaf lay tree leafIdx)) input
          | node lay tree level nodeIdx =>
              exact (OrdinaryCachePreserving.of_splitCachePreserving
                (splitCachePreserving_probeFirstMissingInputCoordinate input 0
                  ((Position.node lay tree level nodeIdx).children.map
                    Coordinate.position))).bind_querying fun _ =>
                      ordinaryCacheQuerying_resolveKnownInput parameter
                        (.position (.node lay tree level nodeIdx)) input
          | ftsLeaf | ftsNode | ftsRoots => exact ordinaryCacheQuerying_splitHashQuery input

theorem ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_probingHashImpl
    (parameter : PublicParameter) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((probingHashImpl parameter input).run cache))) :
    ordinaryQueryCache finalCache = (ordinaryQueryCache cache).cacheQuery input output := by
  exact ordinaryCacheQuerying_probingHashQuery parameter input state cache fuel finalState
    remaining output finalCache hresult

theorem ordinaryCacheQuerying_resolveVerifierInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    OrdinaryCacheQuerying input (resolveVerifierInput parameter coordinate input) := by
  intro state cache fuel finalState remaining output finalCache hresult
  unfold resolveVerifierInput at hresult
  cases hcached : cache (.ordinary input) with
  | some cached =>
      simp [StateT.run_get, hcached, LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      funext other
      by_cases heq : other = input
      · subst other
        simp [QueryCache.cacheQuery, ordinaryQueryCache, hcached]
      · simp [QueryCache.cacheQuery, heq]
  | none =>
      simp [StateT.run_get, hcached] at hresult
      exact (ordinaryCachePreserving_revealTableInputChildren coordinate).bind_querying
        (fun _ => ordinaryCacheQuerying_resolveKnownInput parameter coordinate input)
          state cache fuel finalState remaining output finalCache hresult

theorem ordinaryCacheQuerying_verifierHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    OrdinaryCacheQuerying input (verifierHashQuery parameter input) := by
  unfold verifierHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      exact (OrdinaryCachePreserving.of_splitCachePreserving
        (splitCachePreserving_probe candidate)).bind_querying fun _ =>
          ordinaryCacheQuerying_resolveVerifierInput parameter candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => exact ordinaryCacheQuerying_splitHashQuery input
      | some position =>
          cases position with
          | chain lay tree leafIdx chainIdx step =>
              exact ordinaryCacheQuerying_resolveVerifierInput parameter
                (.position (.chain lay tree leafIdx chainIdx step)) input
          | leaf lay tree leafIdx =>
              exact ordinaryCacheQuerying_resolveVerifierInput parameter
                (.position (.leaf lay tree leafIdx)) input
          | node lay tree level nodeIdx =>
              exact ordinaryCacheQuerying_resolveVerifierInput parameter
                (.position (.node lay tree level nodeIdx)) input
          | ftsLeaf | ftsNode | ftsRoots => exact ordinaryCacheQuerying_splitHashQuery input

theorem ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_verifierHashImpl
    (parameter : PublicParameter) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashImpl parameter input).run cache))) :
    ordinaryQueryCache finalCache = (ordinaryQueryCache cache).cacheQuery input output := by
  exact ordinaryCacheQuerying_verifierHashQuery parameter input state cache fuel finalState
    remaining output finalCache hresult

theorem verifierHashImpl_output_eq_of_cached
    (parameter : PublicParameter) (input : HashInput)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (output cached : HashOutput) (hcached : cache (.ordinary input) = some cached)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashImpl parameter input).run cache))) :
    output = cached := by
  have hresult' : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter input).run cache)) := by
    simpa only [verifierHashImpl] using hresult
  have hreturned := returnsCachedOrdinary_verifierHashQuery parameter input state cache fuel
    finalState remaining output finalCache hresult'
  have hpreserved := ordinaryEntryPreserving_verifierHashQuery parameter input input state cache
    fuel finalState remaining output finalCache cached hcached hresult'
  exact Option.some.inj (hreturned.symm.trans hpreserved)

theorem verifierHashImpl_output_eq_retainedCompletionAnswer_of_uncached
    (parameter : PublicParameter)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (input : HashInput)
    (state queryState completedState : LazyRevealProbe.State Coordinate)
    (cache queryCache rawCache : SplitHashCache) (fuel queryRemaining : Nat)
    (output : HashOutput)
    (huncached : cache (.ordinary input) = none)
    (hquery : LazyRevealProbe.RawResult.done queryState queryRemaining
        (output, queryCache) ∈ support
      (LazyRevealProbe.runRaw state fuel ((verifierHashImpl parameter input).run cache)))
    (hvalues : LazyRevealProbe.ValuesLE queryState completedState)
    (hcached : rawCache (.ordinary input) = some output) :
    output = retainedCompletionAnswer parameter completedState rawCache baseStarts input := by
  apply verifierHashQuery_output_eq_retainedCompletionAnswer_of_uncached parameter baseStarts
    input state queryState completedState cache queryCache rawCache fuel queryRemaining output
      huncached
  · simpa only [verifierHashImpl] using hquery
  · exact hvalues
  · exact hcached

set_option maxRecDepth 50000 in
theorem replay_of_mem_runRaw_verifierHashImpl_of_initial_cacheAnswersAgreeOnRun
    (parameter : PublicParameter)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (computation : OracleComp HashSpec alpha)
    (state finalState completedState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hcompleted : LazyRevealProbe.ValuesLE finalState completedState)
    (hagrees : CacheAnswersAgreeOnRun (ordinaryQueryCache cache)
      (retainedCompletionAnswer parameter completedState finalCache baseStarts) computation)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (verifierHashImpl parameter) computation).run cache))) :
    evalWithAnswerFn (retainedCompletionAnswer parameter completedState finalCache baseStarts)
        computation = value ∧
      CachedRun (ordinaryQueryCache finalCache)
          (retainedCompletionAnswer parameter completedState finalCache baseStarts) computation ∧
      CacheAnswersAgreeOnRun (ordinaryQueryCache finalCache)
        (retainedCompletionAnswer parameter completedState finalCache baseStarts) computation := by
  let f := retainedCompletionAnswer parameter completedState finalCache baseStarts
  change evalWithAnswerFn f computation = value ∧
    CachedRun (ordinaryQueryCache finalCache) f computation ∧
      CacheAnswersAgreeOnRun (ordinaryQueryCache finalCache) f computation
  change CacheAnswersAgreeOnRun (ordinaryQueryCache cache) f computation at hagrees
  induction computation using OracleComp.inductionOn generalizing
      state cache finalState fuel remaining value with
  | pure result =>
      simp [LazyRevealProbe.runRaw] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, by simp [CachedRun, CacheAnswersAgreeOnRun]⟩
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨queryRaw, hquery, hrest⟩ := hresult
      cases queryRaw with
      | stopped hit => simp at hrest
      | done queryState queryRemaining queryResult =>
          rcases queryResult with ⟨answer, queryCache⟩
          have hcacheStep : ordinaryQueryCache queryCache =
              (ordinaryQueryCache cache).cacheQuery input answer :=
            ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_verifierHashImpl parameter input state
              queryState cache queryCache fuel queryRemaining answer hquery
          have hcachedQuery : queryCache (.ordinary input) = some answer := by
            have hpoint := congrFun hcacheStep input
            simpa [ordinaryQueryCache, QueryCache.cacheQuery] using hpoint
          have hcachedFinal : finalCache (.ordinary input) = some answer :=
            (ordinaryEntryPreservingImpl_verifierHashImpl parameter input).simulateQ
              (next answer) queryState queryCache queryRemaining finalState remaining value
                finalCache answer hcachedQuery hrest
          have hfinput : f input = answer := by
            cases hlookup : cache (.ordinary input) with
            | some cached =>
                have hanswer := verifierHashImpl_output_eq_of_cached parameter input state
                  queryState cache queryCache fuel queryRemaining answer cached hlookup hquery
                rw [hanswer]
                exact hagrees input (by rw [queriedInputs_query_bind]; exact List.mem_cons_self)
                  cached hlookup
            | none =>
                have hvaluesQueryFinal := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                  ((simulateQ (verifierHashImpl parameter) (next answer)).run queryCache)
                    queryState finalState queryRemaining remaining (value, finalCache) hrest
                exact (verifierHashImpl_output_eq_retainedCompletionAnswer_of_uncached parameter
                  baseStarts input state queryState completedState cache queryCache finalCache fuel
                    queryRemaining answer hlookup hquery (hvaluesQueryFinal.trans hcompleted)
                      hcachedFinal).symm
          have hagreesTail : CacheAnswersAgreeOnRun (ordinaryQueryCache queryCache) f
              (next answer) := by
            intro query hqueryTail output hcached
            rw [hcacheStep] at hcached
            by_cases heq : query = input
            · subst query
              have houtput : output = answer := by
                exact (Option.some.inj
                  (show some answer = some output by
                    simpa [QueryCache.cacheQuery] using hcached)).symm
              rw [houtput]
              exact hfinput
            · apply hagrees query
              · rw [queriedInputs_query_bind, hfinput]
                exact List.mem_cons_of_mem input hqueryTail
              · simpa [QueryCache.cacheQuery, heq] using hcached
          obtain ⟨htailEval, htailCached, htailAgrees⟩ := ih answer queryState finalState queryCache
            queryRemaining remaining value hcompleted hrest hagreesTail
          constructor
          · rw [evalWithAnswerFn_bind,
              show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
                simulateQ_spec_query f input, hfinput]
            exact htailEval
          · constructor
            · intro other hother
              rw [queriedInputs_query_bind, hfinput] at hother
              simp only [List.mem_cons] at hother
              rcases hother with rfl | htail
              · simp [ordinaryQueryCache, hcachedFinal]
              · exact htailCached other htail
            · intro other hother output hcached
              rw [queriedInputs_query_bind, hfinput] at hother
              simp only [List.mem_cons] at hother
              rcases hother with rfl | htail
              · change finalCache (.ordinary other) = some output at hcached
                rw [hcachedFinal] at hcached
                exact hfinput.trans (Option.some.inj hcached)
              · exact htailAgrees other htail output hcached

theorem verifierHashQuery_returns_table
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (position : Position) (hots : IsOtsPosition position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (hf : (ordinaryQueryCache finalCache).AgreesWithFn f)
    (htable : ∀ coordinate cached, finalState.values coordinate = some cached →
      cached = table coordinate)
    (hrealizes : f (tableInput parameter table (.position position)) =
      table (.position position))
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter
          (tableInput parameter table (.position position))).run cache))) :
    output = table (.position position) ∧
      finalCache (.ordinary (tableInput parameter table (.position position))) = some output := by
  cases hcached : cache (.ordinary
      (tableInput parameter table (.position position))) with
  | none =>
      exact verifierHashQuery_returns_table_of_uncached parameter table position hots state
        finalState cache finalCache fuel remaining output hcached htable hresult
  | some cached =>
      have hreturns := returnsCachedOrdinary_verifierHashQuery parameter
        (tableInput parameter table (.position position)) state cache fuel finalState remaining
          output finalCache hresult
      have hanswer := hf hreturns
      exact ⟨hanswer.symm.trans hrealizes, hreturns⟩

set_option maxRecDepth 10000 in
theorem probingHashQuery_returns_table_of_available
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (hots : IsOtsPosition position)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashOutput)
    (havailable : TableInputAvailable table state (.position position))
    (htable : ∀ other cached, finalState.values other = some cached →
      cached = table other)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((probingHashQuery parameter
          (tableInput parameter table (.position position))).run cache))) :
    output = table (.position position) ∧
      finalCache (.ordinary (tableInput parameter table (.position position))) = some output := by
  let input := tableInput parameter table (.position position)
  have hposition : decodePosition? parameter input = some position :=
    (decodePosition?_eq_some_iff parameter input position).2 ⟨tablePayload table position, rfl⟩
  change LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel ((probingHashQuery parameter input).run cache))
    at hresult
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      unfold probingHashQuery at hresult
      rw [hprobe, hposition] at hresult
      cases position with
      | leaf lay tree leafIdx =>
          simp only at hresult
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
          obtain ⟨probeRaw, hprobeRun, hrest⟩ := hresult
          cases probeRaw with
          | stopped hit => simp at hrest
          | done probeState probeRemaining probeResult =>
              rcases probeResult with ⟨probed, probeCache⟩
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                ((prepareLeafInputProbe input candidate lay tree leafIdx).run cache) state
                  probeState fuel probeRemaining (probed, probeCache) hprobeRun
              have havailableProbe := havailable.monoValues hvaluesLE
              have houtputCoordinate := decodeProbe?_outputCoordinate_eq_position parameter input
                candidate (.leaf lay tree leafIdx) hprobe hposition
              rw [houtputCoordinate] at hrest
              exact resolveKnownInput_returns_table_of_available parameter table
                (.position (.leaf lay tree leafIdx)) probeState finalState probeCache finalCache
                  probeRemaining remaining output havailableProbe htable hrest
      | chain lay tree leafIdx chainIdx step =>
          simp only at hresult
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
          obtain ⟨probeRaw, hprobeRun, hrest⟩ := hresult
          cases probeRaw with
          | stopped hit => simp at hrest
          | done probeState probeRemaining probeResult =>
              rcases probeResult with ⟨probed, probeCache⟩
              have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                ((probe candidate).run cache) state probeState fuel probeRemaining
                  (probed, probeCache) hprobeRun
              have havailableProbe := havailable.monoValues hvaluesLE
              have houtputCoordinate := decodeProbe?_outputCoordinate_eq_position parameter input
                candidate (.chain lay tree leafIdx chainIdx step) hprobe hposition
              rw [houtputCoordinate] at hrest
              exact resolveKnownInput_returns_table_of_available parameter table
                (.position (.chain lay tree leafIdx chainIdx step)) probeState finalState probeCache
                  finalCache probeRemaining remaining output havailableProbe htable hrest
      | node lay tree level nodeIdx =>
          have hnone : decodeProbe? parameter input = none := by
            apply decodeProbe?_tweakableHashInput_of_not_chain_leaf parameter
              (Position.node lay tree level nodeIdx).domain
                (tablePayload table (.node lay tree level nodeIdx))
                  (Position.domain_inRange (.node lay tree level nodeIdx))
            · intro otherLay otherTree otherLeaf otherChain otherStep heq
              simp [Position.domain] at heq
            · intro otherLay otherTree otherLeaf heq
              simp [Position.domain] at heq
          rw [hnone] at hprobe
          simp at hprobe
      | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots
  | none =>
      unfold probingHashQuery at hresult
      rw [hprobe, hposition] at hresult
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only at hresult
          exact resolveKnownInput_returns_table_of_available parameter table
            (.position (.chain lay tree leafIdx chainIdx step)) state finalState cache finalCache
              fuel remaining output havailable htable hresult
      | leaf lay tree leafIdx =>
          simp only at hresult
          exact resolveKnownInput_returns_table_of_available parameter table
            (.position (.leaf lay tree leafIdx)) state finalState cache finalCache fuel remaining
              output havailable htable hresult
      | node lay tree level nodeIdx =>
          simp only at hresult
          let coordinates := (Position.node lay tree level nodeIdx).children.map Coordinate.position
          have hvalues : ∀ coordinate, coordinate ∈ coordinates →
              state.values coordinate = some (table coordinate) := by
            intro coordinate hcoordinate
            obtain ⟨child, hchild, heq⟩ := List.mem_map.1 hcoordinate
            rw [← heq]
            exact havailable child hchild
          have hscan := runRaw_probeFirstMissingInputCoordinate_of_values table input state cache
            fuel 0 coordinates hvalues
          change LazyRevealProbe.RawResult.done finalState remaining
              (output, finalCache) ∈ support (LazyRevealProbe.runRaw state fuel
                ((probeFirstMissingInputCoordinate input 0 coordinates).run cache >>=
                  fun probeResult => (resolveKnownInput parameter
                    (.position (.node lay tree level nodeIdx)) input).run probeResult.2)) at hresult
          rw [LazyRevealProbe.runRaw_bind, hscan, pure_bind] at hresult
          exact resolveKnownInput_returns_table_of_available parameter table
            (.position (.node lay tree level nodeIdx)) state finalState cache finalCache fuel
              remaining output havailable htable hresult
      | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots

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

set_option maxRecDepth 10000 in
theorem probingHashQuery_chain_returns_table_or_pending
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remainingFuel : Nat)
    (output : HashOutput)
    (hstateTable : ∀ coordinate cached,
      state.values coordinate = some cached → cached = table coordinate)
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hrevealed : PublishedValues state)
    (hresult : LazyRevealProbe.RawResult.done finalState remainingFuel
        (output, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((probingHashQuery parameter
          (tableInput parameter table
            (.position (.chain lay tree leafIdx chainIdx step)))).run cache))) :
    output = table (.position (.chain lay tree leafIdx chainIdx step)) ∨
      ∃ coordinate : Coordinate,
        finalState.values coordinate = none ∧
          finalState.hitAt coordinate (table coordinate) := by
  let position : Position := .chain lay tree leafIdx chainIdx step
  let input := tableInput parameter table (.position position)
  let source := chainInputSource lay tree leafIdx chainIdx step
  let candidate := chainInputProbe table lay tree leafIdx chainIdx step
  have hmatches : candidate.MatchesInput parameter input := by
    simpa [candidate, input, position] using
      chainInputProbe_matchesInput parameter table lay tree leafIdx chainIdx step
  have hdecode : decodeProbe? parameter input = some candidate :=
    (decodeProbe?_eq_some_iff parameter input candidate).2 hmatches
  have hposition : decodePosition? parameter input = some position :=
    (decodePosition?_eq_some_iff parameter input position).2
      ⟨tablePayload table position, rfl⟩
  have hsource : candidate.coordinate = source := rfl
  cases hvalue : state.values source with
  | some value =>
      left
      have hvalue' : state.values source = some (table source) := by
        rw [hvalue, hstateTable source value hvalue]
      have havailable : TableInputAvailable table state (.position position) := by
        by_cases hzero : step.val = 0
        · simpa [TableInputAvailable, position, source, chainInputSource, hzero] using hvalue'
        · have hpositive : 0 < step.val := Nat.pos_of_ne_zero hzero
          simp only [position, TableInputAvailable, if_neg hzero]
          intro child hchild
          have hchildEq : .position child = source := by
            simp only [Position.children, dif_pos hpositive,
              List.mem_singleton] at hchild
            subst child
            simp [source, chainInputSource, hzero]
          rw [hchildEq]
          exact hvalue'
      exact (probingHashQuery_returns_table_of_available parameter table position (by trivial)
        state finalState cache finalCache fuel remainingFuel output havailable hfinalTable
          (by simpa [input, position] using hresult)).1
  | none =>
      have hnotRevealed : source ∉ state.revealed := by
        intro hsourceRevealed
        exact (hrevealed source hsourceRevealed) hvalue
      change LazyRevealProbe.RawResult.done finalState remainingFuel (output, finalCache) ∈
        support (LazyRevealProbe.runRaw state fuel
          ((probingHashQuery parameter input).run cache)) at hresult
      unfold probingHashQuery at hresult
      rw [hdecode, hposition, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨probeRaw, hprobe, hresolve⟩ := hresult
      cases probeRaw with
      | stopped hit => simp at hresolve
      | done probeState probeRemaining probeResult =>
          rcases probeResult with ⟨probed, probeCache⟩
          change LazyRevealProbe.RawResult.done probeState probeRemaining
              (probed, probeCache) ∈ support
            (LazyRevealProbe.runRaw state fuel
              (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>=
                fun result => pure (result, cache))) at hprobe
          rw [LazyRevealProbe.probeQuery,
            LazyRevealProbe.runRaw_probe_query_bind] at hprobe
          cases fuel with
          | zero => simp at hprobe
          | succ probeFuel =>
              simp only at hprobe
              rw [hsource, if_neg hnotRevealed] at hprobe
              simp [LazyRevealProbe.runRaw] at hprobe
              rcases hprobe with ⟨rfl, rfl, rfl, rfl⟩
              right
              refine ⟨source, ?_⟩
              have hhit : (state.addPending source candidate.candidate).hitAt source
                  (table source) := by
                rw [LazyRevealProbe.State.hitAt, ← chainInputProbe_candidate table lay tree
                  leafIdx chainIdx step]
                exact LazyRevealProbe.State.pendingAt_addPending_self state source
                  candidate.candidate
              exact LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done
                ((resolveKnownInput parameter candidate.outputCoordinate input).run cache)
                  source (table source) (state.addPending source candidate.candidate) finalState
                    probeRemaining remainingFuel (output, finalCache) (by
                      simpa [LazyRevealProbe.State.addPending] using hvalue) hhit
                        (hfinalTable source) hresolve

set_option maxRecDepth 10000 in
theorem probingHashQuery_node_returns_table_or_pending
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remainingFuel : Nat)
    (output : HashOutput)
    (hstateTable : ∀ position cached,
      state.values (.position position) = some cached →
        cached = table (.position position))
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hrevealed : ∀ coordinate, coordinate ∈ state.revealed →
      state.values coordinate ≠ none)
    (hresult : LazyRevealProbe.RawResult.done finalState remainingFuel
        (output, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((probingHashQuery parameter
          (tableInput parameter table
            (.position (.node lay tree level nodeIdx)))).run cache))) :
    output = table (.position (.node lay tree level nodeIdx)) ∨
      ∃ child : Position,
        finalState.values (.position child) = none ∧
          finalState.hitAt (.position child) (table (.position child)) := by
  let position : Position := .node lay tree level nodeIdx
  let input := tableInput parameter table (.position position)
  rcases positionValues_or_first_missing table state position.children hstateTable with
      havailable | ⟨prior, child, remaining, hchildren, hprior, hmissing⟩
  · left
    exact (probingHashQuery_returns_table_of_available parameter table position (by trivial)
      state finalState cache finalCache fuel remainingFuel output (by
        intro child hchild
        exact havailable child hchild) hfinalTable (by simpa [input, position] using hresult)).1
  · have hnotRevealed : .position child ∉ state.revealed := by
      intro hchild
      exact (hrevealed (.position child) hchild) hmissing
    cases fuel with
    | zero =>
        have hposition : decodePosition? parameter input = some position :=
          (decodePosition?_eq_some_iff parameter input position).2
            ⟨tablePayload table position, rfl⟩
        have hprobe : decodeProbe? parameter input = none := by
          apply decodeProbe?_tweakableHashInput_of_not_chain_leaf parameter position.domain
            (tablePayload table position) position.domain_inRange
          · intro otherLay otherTree otherLeaf otherChain otherStep heq
            simp [position, Position.domain] at heq
          · intro otherLay otherTree otherLeaf heq
            simp [position, Position.domain] at heq
        let priorCoordinates := prior.map Coordinate.position
        let remainingCoordinates := remaining.map Coordinate.position
        have hcoordinates : position.children.map Coordinate.position =
            priorCoordinates ++ .position child :: remainingCoordinates := by
          simp only [hchildren, priorCoordinates, remainingCoordinates, List.map_append,
            List.map_cons]
        have hcoordinateValues : ∀ coordinate, coordinate ∈ priorCoordinates →
            state.values coordinate = some (table coordinate) := by
          intro coordinate hcoordinate
          obtain ⟨other, hother, rfl⟩ := List.mem_map.1 hcoordinate
          exact hprior other hother
        have hscan :=
          runRaw_probeFirstMissingInputCoordinate_zero_of_prefix_values_of_missing table input
            state cache 0 priorCoordinates remainingCoordinates (.position child)
              hcoordinateValues hmissing
        change LazyRevealProbe.RawResult.done finalState remainingFuel (output, finalCache) ∈
          support (LazyRevealProbe.runRaw state 0
            ((probingHashQuery parameter input).run cache)) at hresult
        unfold probingHashQuery at hresult
        rw [hprobe, hposition] at hresult
        simp only [position] at hresult
        rw [hcoordinates, StateT.run_bind, LazyRevealProbe.runRaw_bind, hscan] at hresult
        simp at hresult
    | succ fuel =>
        have hpending := probingHashQuery_node_pending_of_prefix_values_of_missing parameter table
          lay tree level nodeIdx state finalState cache finalCache fuel remainingFuel prior
            remaining child output hchildren hprior hmissing hnotRevealed (by
              simpa [input, position, Nat.succ_eq_add_one] using hresult)
        right
        refine ⟨child, ?_, ?_⟩
        · rw [hpending.1]
          simpa [LazyRevealProbe.State.addPending] using hmissing
        · rw [hpending.1, LazyRevealProbe.State.hitAt]
          exact LazyRevealProbe.State.pendingAt_addPending_self state (.position child)
            (truncateHash (table (.position child)))

set_option maxRecDepth 10000 in
theorem probingHashQuery_leaf_returns_table_or_pending
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remainingFuel : Nat)
    (output : HashOutput)
    (hstateTable : ∀ position cached,
      state.values (.position position) = some cached →
        cached = table (.position position))
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hrevealed : ∀ coordinate, coordinate ∈ state.revealed →
      state.values coordinate ≠ none)
    (hresult : LazyRevealProbe.RawResult.done finalState remainingFuel
        (output, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((probingHashQuery parameter
          (tableInput parameter table
            (.position (.leaf lay tree leafIdx)))).run cache))) :
    output = table (.position (.leaf lay tree leafIdx)) ∨
      ∃ child : Position,
        finalState.values (.position child) = none ∧
          finalState.hitAt (.position child) (table (.position child)) := by
  let position : Position := .leaf lay tree leafIdx
  let input := tableInput parameter table (.position position)
  rcases positionValues_or_first_missing table state position.children hstateTable with
      havailable | ⟨prior, child, remaining, hchildren, hprior, hmissing⟩
  · left
    exact (probingHashQuery_returns_table_of_available parameter table position (by trivial)
      state finalState cache finalCache fuel remainingFuel output (by
        intro child hchild
        exact havailable child hchild) hfinalTable (by simpa [input, position] using hresult)).1
  · have hnotRevealed : .position child ∉ state.revealed := by
      intro hchild
      exact (hrevealed (.position child) hchild) hmissing
    cases fuel with
    | zero =>
        let candidate : Probe :=
          ⟨.position (.chain lay tree leafIdx ⟨0, by norm_num [numChains]⟩
            Position.lastChainStep), slotDigest 0 input⟩
        have hprobe : decodeProbe? parameter input = some candidate := by
          apply (decodeProbe?_eq_some_iff parameter input candidate).2
          simp only [candidate, Probe.MatchesInput]
          rw [dif_neg (by simp [Position.lastChainStep, chainLength, winternitzBits])]
          exact ⟨trivial, tablePayload table position, rfl, trivial⟩
        have hposition : decodePosition? parameter input = some position :=
          (decodePosition?_eq_some_iff parameter input position).2
            ⟨tablePayload table position, rfl⟩
        have hprepare :=
          runRaw_prepareLeafInputProbe_zero_of_prefix_values_of_missing parameter table lay tree
            leafIdx candidate state cache prior remaining child (by simpa [input, position]
              using hprobe) hchildren hprior hmissing
        change LazyRevealProbe.RawResult.done finalState remainingFuel (output, finalCache) ∈
          support (LazyRevealProbe.runRaw state 0
            ((probingHashQuery parameter input).run cache)) at hresult
        unfold probingHashQuery at hresult
        rw [hprobe, hposition] at hresult
        simp only [position] at hresult
        rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, hprepare] at hresult
        simp at hresult
    | succ fuel =>
        have hpending := probingHashQuery_leaf_pending_of_prefix_values_of_missing parameter table
          lay tree leafIdx state finalState cache finalCache fuel remainingFuel prior remaining child
            output hchildren hprior hmissing hnotRevealed (by
              simpa [input, position, Nat.succ_eq_add_one] using hresult)
        right
        refine ⟨child, ?_, ?_⟩
        · rw [hpending.1]
          simpa [LazyRevealProbe.State.addPending] using hmissing
        · rw [hpending.1, LazyRevealProbe.State.hitAt]
          exact LazyRevealProbe.State.pendingAt_addPending_self state (.position child)
            (truncateHash (table (.position child)))

def IsCanonicalOtsPosition : Position → Prop
  | .chain _ _ _ _ _ | .leaf _ _ _ | .node _ _ _ _ => True
  | _ => False

def CanonicalInputProtected (table : Coordinate → HashOutput)
    (input : HashInput) (position : Position)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) : Prop :=
  cache (.ordinary input) = none ∨
    cache (.ordinary input) = some (table (.position position)) ∨
      ∃ coordinate : Coordinate,
        state.values coordinate = none ∧
          state.hitAt coordinate (table coordinate)

set_option maxRecDepth 10000 in
theorem canonicalInputProtected_probingHashQuery
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (input query : HashInput) (position : Position) (hkind : IsCanonicalOtsPosition position)
    (hinput : input = tableInput parameter table (.position position))
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashSpec query)
    (hprotected : CanonicalInputProtected table input position state cache)
    (hstateTable : ∀ coordinate cached,
      state.values coordinate = some cached → cached = table coordinate)
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hrevealed : PublishedValues state)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((probingHashQuery parameter query).run cache))) :
    CanonicalInputProtected table input position finalState finalCache := by
  rcases hprotected with hnone | hexact | ⟨coordinate, hmissing, hhit⟩
  · by_cases heq : query = input
    · subst query
      have hlocal : output = table (.position position) ∨
          ∃ coordinate : Coordinate,
            finalState.values coordinate = none ∧
              finalState.hitAt coordinate (table coordinate) := by
        subst input
        cases position with
        | chain lay tree leafIdx chainIdx step =>
            exact probingHashQuery_chain_returns_table_or_pending parameter table lay tree leafIdx
              chainIdx step state finalState cache finalCache fuel remaining output hstateTable
                hfinalTable hrevealed hresult
        | leaf lay tree leafIdx =>
            rcases probingHashQuery_leaf_returns_table_or_pending parameter table lay tree leafIdx
              state finalState cache finalCache fuel remaining output (by
                intro child cached hcached
                exact hstateTable (.position child) cached hcached) hfinalTable hrevealed hresult with
              houtput | ⟨child, hmissing, hhit⟩
            · exact Or.inl houtput
            · exact Or.inr ⟨.position child, hmissing, hhit⟩
        | node lay tree level nodeIdx =>
            rcases probingHashQuery_node_returns_table_or_pending parameter table lay tree level
              nodeIdx state finalState cache finalCache fuel remaining output (by
                intro child cached hcached
                exact hstateTable (.position child) cached hcached) hfinalTable hrevealed hresult with
              houtput | ⟨child, hmissing, hhit⟩
            · exact Or.inl houtput
            · exact Or.inr ⟨.position child, hmissing, hhit⟩
        | ftsLeaf | ftsNode | ftsRoots => simp [IsCanonicalOtsPosition] at hkind
      rcases hlocal with houtput | hpending
      · right
        left
        have hcache := ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_probingHashImpl parameter
          input state finalState cache finalCache fuel remaining output hresult
        change finalCache (.ordinary input) = some (table (.position position))
        change ordinaryQueryCache finalCache input = some (table (.position position))
        rw [hcache]
        simp [QueryCache.cacheQuery, houtput]
      · exact Or.inr (Or.inr hpending)
    · left
      have hcache := ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_probingHashImpl parameter
        query state finalState cache finalCache fuel remaining output hresult
      change finalCache (.ordinary input) = none
      change ordinaryQueryCache finalCache input = none
      rw [hcache]
      rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq)]
      exact hnone
  · by_cases heq : query = input
    · subst query
      have hlocal : output = table (.position position) ∨
          ∃ coordinate : Coordinate,
            finalState.values coordinate = none ∧
              finalState.hitAt coordinate (table coordinate) := by
        subst input
        cases position with
        | chain lay tree leafIdx chainIdx step =>
            exact probingHashQuery_chain_returns_table_or_pending parameter table lay tree leafIdx
              chainIdx step state finalState cache finalCache fuel remaining output hstateTable
                hfinalTable hrevealed hresult
        | leaf lay tree leafIdx =>
            rcases probingHashQuery_leaf_returns_table_or_pending parameter table lay tree leafIdx
              state finalState cache finalCache fuel remaining output (by
                intro child cached hcached
                exact hstateTable (.position child) cached hcached) hfinalTable hrevealed hresult with
              houtput | ⟨child, hmissing, hhit⟩
            · exact Or.inl houtput
            · exact Or.inr ⟨.position child, hmissing, hhit⟩
        | node lay tree level nodeIdx =>
            rcases probingHashQuery_node_returns_table_or_pending parameter table lay tree level
              nodeIdx state finalState cache finalCache fuel remaining output (by
                intro child cached hcached
                exact hstateTable (.position child) cached hcached) hfinalTable hrevealed hresult with
              houtput | ⟨child, hmissing, hhit⟩
            · exact Or.inl houtput
            · exact Or.inr ⟨.position child, hmissing, hhit⟩
        | ftsLeaf | ftsNode | ftsRoots => simp [IsCanonicalOtsPosition] at hkind
      rcases hlocal with houtput | hpending
      · right
        left
        have hcache := ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_probingHashImpl parameter
          input state finalState cache finalCache fuel remaining output hresult
        change finalCache (.ordinary input) = some (table (.position position))
        change ordinaryQueryCache finalCache input = some (table (.position position))
        rw [hcache]
        simp [QueryCache.cacheQuery, houtput]
      · exact Or.inr (Or.inr hpending)
    · right
      left
      have hcache := ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_probingHashImpl parameter
        query state finalState cache finalCache fuel remaining output hresult
      change finalCache (.ordinary input) = some (table (.position position))
      change ordinaryQueryCache finalCache input = some (table (.position position))
      rw [hcache]
      rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq)]
      exact hexact
  · right
    right
    have hpersist := LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done
      ((probingHashQuery parameter query).run cache) coordinate
        (table coordinate) state finalState fuel remaining (output, finalCache)
          hmissing hhit (hfinalTable coordinate) hresult
    exact ⟨coordinate, hpersist⟩

theorem canonicalInputProtected_of_cache_status_preserved
    (table : Coordinate → HashOutput) (input : HashInput) (position : Position)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (habsence : PreservesOrdinaryAbsence input computation)
    (hentry : OrdinaryEntryPreserving input computation)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hprotected : CanonicalInputProtected table input position state cache)
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache))) :
    CanonicalInputProtected table input position finalState finalCache := by
  rcases hprotected with hnone | hexact | ⟨coordinate, hmissing, hhit⟩
  · left
    exact habsence state cache fuel finalState remaining value finalCache hnone hresult
  · right
    left
    exact hentry state cache fuel finalState remaining value finalCache
      (table (.position position)) hexact hresult
  · right
    right
    have hpersist := LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done
      (computation.run cache) coordinate (table coordinate) state finalState fuel
        remaining (value, finalCache) hmissing hhit (hfinalTable coordinate) hresult
    exact ⟨coordinate, hpersist⟩

theorem OrdinaryCachePreserving.entryPreserving
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    (hpreserves : OrdinaryCachePreserving computation) (input : HashInput) :
    OrdinaryEntryPreserving input computation := by
  intro state cache fuel finalState remaining value finalCache output hcached hresult
  change ordinaryQueryCache finalCache input = some output
  rw [hpreserves state cache fuel finalState remaining value finalCache hresult]
  exact hcached

theorem not_stableOrdinaryInput_of_canonical_ots_tableInput
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (position : Position) (hkind : IsCanonicalOtsPosition position) :
    ¬StableOrdinaryInput parameter
      (tableInput parameter table (.position position)) := by
  intro hstable
  have hposition : decodePosition? parameter
      (tableInput parameter table (.position position)) = some position :=
    (decodePosition?_eq_some_iff parameter _ position).2
      ⟨tablePayload table position, rfl⟩
  apply hstable.2 position hposition
  cases position <;> simp [IsCanonicalOtsPosition, IsOtsPosition] at hkind ⊢

theorem canonicalInputProtected_splitUniformImpl
    (table : Coordinate → HashOutput) (input : HashInput) (position : Position)
    (n : Nat) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : unifSpec n)
    (hprotected : CanonicalInputProtected table input position state cache)
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))) :
    CanonicalInputProtected table input position finalState finalCache := by
  have hpreserves : OrdinaryCachePreserving (splitUniformImpl n) := by
    have hbase := ordinaryCachePreserving_simulateQ_splitUniformImpl
      (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
    simpa [splitUniformImpl] using hbase
  exact canonicalInputProtected_of_cache_status_preserved table input position
    (splitUniformImpl n) (hpreserves.preservesAbsence input) (hpreserves.entryPreserving input)
      state finalState cache finalCache fuel remaining output hprotected hfinalTable hresult

theorem canonicalInputProtected_maskedSigningImpl
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (position : Position) (hkind : IsCanonicalOtsPosition position)
    (hinput : input = tableInput parameter table (.position position))
    (message : SignRequest) (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (output : SigningSpec message)
    (hprotected : CanonicalInputProtected table input position state cache)
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((maskedSigningImpl parameter root ftsSecret message).run cache))) :
    CanonicalInputProtected table input position finalState finalCache := by
  have hnotStable : ¬StableOrdinaryInput parameter input := by
    subst input
    exact not_stableOrdinaryInput_of_canonical_ots_tableInput parameter table position hkind
  exact canonicalInputProtected_of_cache_status_preserved table input position
    (maskedSigningImpl parameter root ftsSecret message)
      (preservesOrdinaryAbsence_maskedSigningImpl parameter root ftsSecret input hnotStable message)
      (ordinaryEntryPreservingImpl_maskedSigningImpl parameter root ftsSecret input message)
      state finalState cache finalCache fuel remaining output hprotected hfinalTable hresult

def PreservesCanonicalInputProtected
    (table : Coordinate → HashOutput) (input : HashInput) (position : Position)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    CanonicalInputProtected table input position state cache →
    (∀ coordinate cached,
      state.values coordinate = some cached → cached = table coordinate) →
    (∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate) →
    PublishedValues state →
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    PublishedValues finalState ∧
      CanonicalInputProtected table input position finalState finalCache

theorem PreservesCanonicalInputProtected.pure
    (table : Coordinate → HashOutput) (input : HashInput) (position : Position)
    (value : alpha) :
    PreservesCanonicalInputProtected table input position
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hprotected _ _ hpublished hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨hpublished, hprotected⟩

theorem PreservesCanonicalInputProtected.bind
    {table : Coordinate → HashOutput} {input : HashInput} {position : Position}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesCanonicalInputProtected table input position left)
    (hnext : ∀ value, PreservesCanonicalInputProtected table input position (next value)) :
    PreservesCanonicalInputProtected table input position (left >>= next) := by
  intro state cache fuel finalState remaining value finalCache hprotected hstateTable hfinalTable
    hpublished hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((next middleValue).run middleCache) middleState finalState middleRemaining remaining
          (value, finalCache) hrest
      have hmiddleTable : ∀ coordinate cached,
          middleState.values coordinate = some cached → cached = table coordinate := by
        intro coordinate cached hcached
        exact hfinalTable coordinate cached (hvaluesLE coordinate cached hcached)
      have hmiddle := hleft state cache fuel middleState middleRemaining middleValue middleCache
        hprotected hstateTable hmiddleTable hpublished hraw
      exact hnext middleValue middleState middleCache middleRemaining finalState remaining value
        finalCache hmiddle.2 hmiddleTable hfinalTable hmiddle.1 hrest

def PreservesCanonicalInputProtectedImpl {spec : OracleSpec ι}
    (table : Coordinate → HashOutput) (input : HashInput) (position : Position)
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, PreservesCanonicalInputProtected table input position (impl query)

theorem PreservesCanonicalInputProtectedImpl.simulateQ {spec : OracleSpec ι}
    {table : Coordinate → HashOutput} {input : HashInput} {position : Position}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : PreservesCanonicalInputProtectedImpl table input position impl)
    (computation : OracleComp spec alpha) :
    PreservesCanonicalInputProtected table input position (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact PreservesCanonicalInputProtected.pure table input position value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem preservesCanonicalInputProtectedImpl_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (position : Position) (hkind : IsCanonicalOtsPosition position)
    (hinput : input = tableInput parameter table (.position position)) :
    PreservesCanonicalInputProtectedImpl table input position
      (maskedExpandedAdversaryImpl parameter root ftsSecret) := by
  intro query
  cases query with
  | inl query =>
      cases query with
      | inl n =>
          intro state cache fuel finalState remaining output finalCache hprotected _ hfinalTable
            hpublished hresult
          refine ⟨(preservesPublishedValuesImpl_splitUniformImpl n state cache fuel finalState
            remaining output finalCache hpublished hresult), ?_⟩
          exact canonicalInputProtected_splitUniformImpl table input position n state finalState
            cache finalCache fuel remaining output hprotected hfinalTable hresult
      | inr query =>
          intro state cache fuel finalState remaining output finalCache hprotected hstateTable
            hfinalTable hpublished hresult
          refine ⟨(preservesPublishedValues_probingHashQuery parameter query state cache fuel
            finalState remaining output finalCache hpublished hresult), ?_⟩
          exact canonicalInputProtected_probingHashQuery parameter table input query position hkind
            hinput state finalState cache finalCache fuel remaining output hprotected hstateTable
              hfinalTable hpublished hresult
  | inr message =>
      intro state cache fuel finalState remaining output finalCache hprotected _ hfinalTable
        hpublished hresult
      refine ⟨(preservesPublishedValues_maskedSigningImpl parameter root ftsSecret message
        state cache fuel finalState remaining output finalCache hpublished hresult), ?_⟩
      exact canonicalInputProtected_maskedSigningImpl parameter table root ftsSecret input position
        hkind hinput message state finalState cache finalCache fuel remaining output hprotected
          hfinalTable hresult

theorem canonicalInputProtected_simulateQ_maskedExpandedAdversaryImpl
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (position : Position) (hkind : IsCanonicalOtsPosition position)
    (hinput : input = tableInput parameter table (.position position))
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hprotected : CanonicalInputProtected table input position state cache)
    (hstateTable : ∀ coordinate cached,
      state.values coordinate = some cached → cached = table coordinate)
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hrevealed : PublishedValues state)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          computation).run cache))) :
    CanonicalInputProtected table input position finalState finalCache :=
  ((preservesCanonicalInputProtectedImpl_maskedExpandedAdversaryImpl parameter table root
    ftsSecret input position hkind hinput).simulateQ computation state cache fuel finalState
      remaining value finalCache hprotected hstateTable hfinalTable hrevealed hresult).2

set_option maxRecDepth 10000 in
theorem canonicalInputProtected_before_verifier_of_mem_runRaw_maskedRetainedGame
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (position : Position) (hkind : IsCanonicalOtsPosition position)
    (hinput : input = tableInput parameter table (.position position))
    (fuel remaining : Nat) (rawState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (htable : ∀ coordinate output, rawState.values coordinate = some output →
      output = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache))) :
    ∃ verifierState verifierFuel verifierCache,
      CanonicalInputProtected table input position verifierState verifierCache ∧
      PublishedValues verifierState ∧
      LazyRevealProbe.RawResult.done rawState remaining (verified, rawCache) ∈ support
        (LazyRevealProbe.runRaw verifierState verifierFuel
          ((simulateQ (verifierRomImpl parameter)
            (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
              verifierCache)) := by
  let rootCoordinate : Coordinate := .position (.node topLayer rootTree
    ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0)
  unfold maskedRetainedGameAfterFtsSecrets at hresult
  rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨rootRaw, hroot, hafterRoot⟩ := hresult
  cases rootRaw with
  | stopped hit => simp at hafterRoot
  | done rootState rootRemaining rootResult =>
      rcases rootResult with ⟨sampledRoot, rootCache⟩
      simp only at hafterRoot
      rw [StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hafterRoot
      obtain ⟨publishRaw, hpublish, hafterPublish⟩ := hafterRoot
      cases publishRaw with
      | stopped hit => simp at hafterPublish
      | done publishState publishRemaining publishResult =>
          rcases publishResult with ⟨publishedUnit, publishCache⟩
          simp only at hafterPublish
          rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterPublish
          obtain ⟨restRaw, hrest, hfinish⟩ := hafterPublish
          cases restRaw with
          | stopped hit => simp at hfinish
          | done restState restRemaining restResult =>
              rcases restResult with ⟨⟨prefixForgery, prefixLog⟩, restCache⟩
              simp only at hfinish
              rw [StateT.run_bind, LazyRevealProbe.runRaw_bind,
                mem_support_bind_iff] at hfinish
              obtain ⟨verifyRaw, hverify, hreturn⟩ := hfinish
              cases verifyRaw with
              | stopped hit => simp at hreturn
              | done verifyState verifyRemaining verifyResult =>
                  rcases verifyResult with ⟨prefixVerified, verifyCache⟩
                  simp [LazyRevealProbe.runRaw] at hreturn
                  rcases hreturn with ⟨rfl, rfl, houtput, rfl⟩
                  rcases houtput with ⟨hrootEq, hrestEq, rfl⟩
                  rcases hrestEq with ⟨rfl, rfl⟩
                  have hvaluesRestRaw := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                    ((simulateQ (verifierRomImpl parameter)
                      (scheme.verify ⟨sampledRoot, parameter⟩ forgery.message
                        forgery.signature)).run restCache)
                    restState rawState restRemaining remaining (verified, rawCache) hverify
                  have htableRest : ∀ coordinate output,
                      restState.values coordinate = some output →
                        output = table coordinate := by
                    intro coordinate output hvalue
                    exact htable coordinate output (hvaluesRestRaw coordinate output hvalue)
                  have hvaluesPublishRest := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                    ((simulateQ (maskedExpandedAdversaryImpl parameter sampledRoot ftsSecret)
                      (signingTraceComputation
                        (adversary.main ⟨sampledRoot, parameter⟩))).run publishCache)
                    publishState restState publishRemaining restRemaining
                      ((forgery, signingLog), restCache) hrest
                  have htablePublish : ∀ coordinate output,
                      publishState.values coordinate = some output →
                        output = table coordinate := by
                    intro coordinate output hvalue
                    exact htableRest coordinate output
                      (hvaluesPublishRest coordinate output hvalue)
                  have hpublishedEmpty : PublishedValues
                      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) := by
                    intro coordinate hcoordinate
                    simp [LazyRevealProbe.State.empty] at hcoordinate
                  have hpublishedRoot := preservesPublishedValues_maskedTreeRoot topLayer rootTree
                    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
                      emptySplitHashCache fuel rootState rootRemaining sampledRoot rootCache
                        hpublishedEmpty hroot
                  obtain ⟨rootOutput, _, hrootValue, _⟩ :=
                    mem_runRaw_maskedTreeRoot_hidden topLayer rootTree
                      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) rootState
                        emptySplitHashCache rootCache fuel rootRemaining sampledRoot hroot
                  have hrootCoordinate :
                      maskedTreeRootCoordinate topLayer rootTree = rootCoordinate := by
                    simp [maskedTreeRootCoordinate, maskedTreeRootLevel, rootCoordinate,
                      layerHeight, topLayer, maxLayerHeight]
                  have hrootValue' : rootState.values rootCoordinate ≠ none := by
                    rw [← hrootCoordinate, hrootValue]
                    simp
                  have hpublishedPublish := publishedValues_of_mem_runRaw_publishCoordinate
                    rootCoordinate rootState publishState rootCache publishCache rootRemaining
                      publishRemaining publishedUnit hpublishedRoot hrootValue'
                        (by simpa [rootCoordinate] using hpublish)
                  have hrootOrdinary := ordinaryCachePreserving_maskedTreeRoot topLayer rootTree
                    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
                      emptySplitHashCache fuel rootState rootRemaining sampledRoot rootCache hroot
                  have hpublishCache := splitCachePreserving_publishCoordinate rootCoordinate
                    rootState rootCache rootRemaining publishState publishRemaining publishedUnit
                      publishCache (by simpa [rootCoordinate] using hpublish)
                  have hinitialProtected : CanonicalInputProtected table input position
                      publishState publishCache := by
                    left
                    rw [hpublishCache]
                    change ordinaryQueryCache rootCache input = none
                    rw [hrootOrdinary]
                    simp [ordinaryQueryCache, emptySplitHashCache]
                  have hprotectedRest :=
                    canonicalInputProtected_simulateQ_maskedExpandedAdversaryImpl parameter table
                      sampledRoot ftsSecret input position hkind hinput
                        (signingTraceComputation
                          (adversary.main ⟨sampledRoot, parameter⟩))
                        publishState restState publishCache restCache publishRemaining
                          restRemaining (forgery, signingLog) hinitialProtected htablePublish
                            htableRest hpublishedPublish hrest
                  exact ⟨restState, restRemaining, restCache, hprotectedRest,
                    (preservesPublishedValuesImpl_maskedExpandedAdversaryImpl parameter sampledRoot
                      ftsSecret).simulateQ
                        (signingTraceComputation (adversary.main ⟨sampledRoot, parameter⟩))
                          publishState publishCache publishRemaining restState restRemaining
                            (forgery, signingLog) restCache hpublishedPublish hrest,
                    by simpa only [hrootEq] using hverify⟩

def CanonicalCacheExactOrAbsent (table : Coordinate → HashOutput)
    (input : HashInput) (position : Position) (cache : SplitHashCache) : Prop :=
  cache (.ordinary input) = none ∨
    cache (.ordinary input) = some (table (.position position))

theorem canonicalCacheExactOrAbsent_verifierHashQuery
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (input query : HashInput) (position : Position) (hkind : IsCanonicalOtsPosition position)
    (hinput : input = tableInput parameter table (.position position))
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (output : HashSpec query)
    (hinitial : CanonicalCacheExactOrAbsent table input position cache)
    (hfinalTable : ∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (output, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((verifierHashQuery parameter query).run cache))) :
    CanonicalCacheExactOrAbsent table input position finalCache := by
  rcases hinitial with hnone | hexact
  · by_cases heq : query = input
    · subst query
      subst input
      right
      have hots : IsOtsPosition position := by
        cases position <;> simp [IsCanonicalOtsPosition, IsOtsPosition] at hkind ⊢
      have hreturns := verifierHashQuery_returns_table_of_uncached parameter table position hots
        state finalState cache finalCache fuel remaining output hnone hfinalTable hresult
      simpa [hreturns.1] using hreturns.2
    · left
      have hcache := ordinaryQueryCache_eq_cacheQuery_of_mem_runRaw_verifierHashImpl parameter
        query state finalState cache finalCache fuel remaining output (by
          simpa only [verifierHashImpl] using hresult)
      change ordinaryQueryCache finalCache input = none
      rw [hcache, QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq)]
      exact hnone
  · right
    exact ordinaryEntryPreserving_verifierHashQuery parameter input query state cache fuel
      finalState remaining output finalCache (table (.position position)) hexact hresult

def PreservesCanonicalCacheExactOrAbsent
    (table : Coordinate → HashOutput) (input : HashInput) (position : Position)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ state cache fuel finalState remaining value finalCache,
    CanonicalCacheExactOrAbsent table input position cache →
    (∀ coordinate cached,
      finalState.values coordinate = some cached → cached = table coordinate) →
    LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel (computation.run cache)) →
    CanonicalCacheExactOrAbsent table input position finalCache

theorem PreservesCanonicalCacheExactOrAbsent.pure
    (table : Coordinate → HashOutput) (input : HashInput) (position : Position)
    (value : alpha) :
    PreservesCanonicalCacheExactOrAbsent table input position
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro state cache fuel finalState remaining result finalCache hinitial _ hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  exact hinitial

theorem PreservesCanonicalCacheExactOrAbsent.bind
    {table : Coordinate → HashOutput} {input : HashInput} {position : Position}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : PreservesCanonicalCacheExactOrAbsent table input position left)
    (hnext : ∀ value, PreservesCanonicalCacheExactOrAbsent table input position (next value)) :
    PreservesCanonicalCacheExactOrAbsent table input position (left >>= next) := by
  intro state cache fuel finalState remaining value finalCache hinitial hfinalTable hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈ support
    (LazyRevealProbe.runRaw state fuel
      (left.run cache >>= fun result => (next result.1).run result.2)) at hresult
  rw [LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hresult
  obtain ⟨raw, hraw, hrest⟩ := hresult
  cases raw with
  | stopped hit => simp at hrest
  | done middleState middleRemaining middleResult =>
      rcases middleResult with ⟨middleValue, middleCache⟩
      have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
        ((next middleValue).run middleCache) middleState finalState middleRemaining remaining
          (value, finalCache) hrest
      have hmiddleTable : ∀ coordinate cached,
          middleState.values coordinate = some cached → cached = table coordinate := by
        intro coordinate cached hcached
        exact hfinalTable coordinate cached (hvaluesLE coordinate cached hcached)
      exact hnext middleValue middleState middleCache middleRemaining finalState remaining value
        finalCache (hleft state cache fuel middleState middleRemaining middleValue middleCache
          hinitial hmiddleTable hraw) hfinalTable hrest

def PreservesCanonicalCacheExactOrAbsentImpl {spec : OracleSpec ι}
    (table : Coordinate → HashOutput) (input : HashInput) (position : Position)
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, PreservesCanonicalCacheExactOrAbsent table input position (impl query)

theorem PreservesCanonicalCacheExactOrAbsentImpl.simulateQ {spec : OracleSpec ι}
    {table : Coordinate → HashOutput} {input : HashInput} {position : Position}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : PreservesCanonicalCacheExactOrAbsentImpl table input position impl)
    (computation : OracleComp spec alpha) :
    PreservesCanonicalCacheExactOrAbsent table input position (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact PreservesCanonicalCacheExactOrAbsent.pure table input position value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem preservesCanonicalCacheExactOrAbsentImpl_verifierRomImpl
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (input : HashInput) (position : Position) (hkind : IsCanonicalOtsPosition position)
    (hinput : input = tableInput parameter table (.position position)) :
    PreservesCanonicalCacheExactOrAbsentImpl table input position
      (verifierRomImpl parameter) := by
  intro query
  cases query with
  | inl n =>
      intro state cache fuel finalState remaining output finalCache hinitial hfinalTable hresult
      have hpreserves : OrdinaryCachePreserving (splitUniformImpl n) := by
        have hbase := ordinaryCachePreserving_simulateQ_splitUniformImpl
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
        simpa [splitUniformImpl] using hbase
      rcases hinitial with hnone | hexact
      · left
        exact hpreserves.preservesAbsence input state cache fuel finalState remaining output
          finalCache hnone hresult
      · right
        exact hpreserves.entryPreserving input state cache fuel finalState remaining output
          finalCache (table (.position position)) hexact hresult
  | inr query =>
      intro state cache fuel finalState remaining output finalCache hinitial hfinalTable hresult
      exact canonicalCacheExactOrAbsent_verifierHashQuery parameter table input query position
        hkind hinput state finalState cache finalCache fuel remaining output hinitial hfinalTable
          hresult

set_option maxRecDepth 10000 in
theorem cached_tableInput_eq_of_canonical_ots_of_clean_finalize
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (position : Position) (hkind : IsCanonicalOtsPosition position)
    (hinput : input = tableInput parameter table (.position position))
    (fuel remaining : Nat)
    (rawState completedState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool) (output : HashOutput)
    (hcompletedTable : ∀ coordinate cached,
      completedState.values coordinate = some cached → cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hcached : rawCache (.ordinary input) = some output) :
    output = table (.position position) := by
  have hrawTable : ∀ coordinate cached,
      rawState.values coordinate = some cached → cached = table coordinate := by
    intro coordinate cached hvalue
    exact hcompletedTable coordinate cached
      (finalizeDetailedFrom_preserves_value rawState.coordinates.toList rawState completedState
        coordinate cached hvalue hfinalize)
  obtain ⟨verifierState, verifierFuel, verifierCache, hprotected, _, hverify⟩ :=
    canonicalInputProtected_before_verifier_of_mem_runRaw_maskedRetainedGame adversary parameter
      table ftsSecret input position hkind hinput fuel remaining rawState rawCache root forgery
        signingLog verified hrawTable hresult
  rcases hprotected with hnone | hexact | ⟨coordinate, hmissing, hhit⟩
  · have hterminal :=
      (preservesCanonicalCacheExactOrAbsentImpl_verifierRomImpl parameter table input position
        hkind hinput).simulateQ
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
            verifierState verifierCache verifierFuel rawState remaining verified rawCache
              (Or.inl hnone) hrawTable hverify
    rcases hterminal with hterminal | hterminal
    · rw [hcached] at hterminal
      simp at hterminal
    · exact Option.some.inj (hcached.symm.trans hterminal)
  · have hterminal :=
      (preservesCanonicalCacheExactOrAbsentImpl_verifierRomImpl parameter table input position
        hkind hinput).simulateQ
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
            verifierState verifierCache verifierFuel rawState remaining verified rawCache
              (Or.inr hexact) hrawTable hverify
    rcases hterminal with hterminal | hterminal
    · rw [hcached] at hterminal
      simp at hterminal
    · exact Option.some.inj (hcached.symm.trans hterminal)
  · have hpersist := LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done
      ((simulateQ (verifierRomImpl parameter)
        (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
          verifierCache)
        coordinate (table coordinate) verifierState rawState verifierFuel remaining
          (verified, rawCache) hmissing hhit (hrawTable coordinate) hverify
    exact (finalizeDetailed_false_of_pending_hit table rawState completedState coordinate
      hpersist.1 hpersist.2 (hcompletedTable coordinate) hfinalize).elim

set_option maxRecDepth 10000 in
theorem exactMaterializedCacheConsistent_of_clean_finalize
    (adversary : Adversary) (parameter : PublicParameter)
    (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel remaining : Nat)
    (rawState completedState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hcompletedTable : ∀ coordinate cached,
      completedState.values coordinate = some cached → cached = table coordinate)
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState)) :
    ExactMaterializedCacheConsistent parameter table completedState rawCache := by
  intro input position output hots _ hinput _ hcached
  have hkind : IsCanonicalOtsPosition position := by
    cases position <;> simp [IsOtsPosition, IsCanonicalOtsPosition] at hots ⊢
  exact cached_tableInput_eq_of_canonical_ots_of_clean_finalize adversary parameter table
    ftsSecret input position hkind hinput fuel remaining rawState completedState rawCache root
      forgery signingLog verified output hcompletedTable hresult hfinalize hcached

theorem simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hchain : ∀ lay tree leafIdx chainIdx step,
      domain ≠ .chain lay tree leafIdx chainIdx step)
    (hleaf : ∀ lay tree leafIdx, domain ≠ .leaf lay tree leafIdx)
    (hnode : ∀ lay tree level nodeIdx, domain ≠ .node lay tree level nodeIdx) :
    simulateQ (probingHashImpl parameter) (tweakableHash parameter domain payload) =
      simulateQ ordinaryHashImpl (tweakableHash parameter domain payload) := by
  unfold tweakableHash oracleHash
  rw [simulateQ_bind, simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query, simulateQ_pure]
  rw [probingHashImpl_eq_ordinaryHashImpl_of_stable parameter _
    (stableOrdinaryInput_tweakableHashInput parameter domain payload hinRange
      hchain hleaf hnode)]

theorem simulateQ_probingHashImpl_messageDigest_eq_ordinaryHashImpl
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    simulateQ (probingHashImpl parameter)
        (messageDigest parameter root message randomness) =
      simulateQ ordinaryHashImpl
        (messageDigest parameter root message randomness) := by
  unfold messageDigest oracleHash
  rw [simulateQ_bind, simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query, simulateQ_pure]
  rw [probingHashImpl_eq_ordinaryHashImpl_of_stable parameter _
    (stableOrdinaryInput_tweakableHashInput parameter .message _ (by trivial)
      (by simp) (by simp) (by simp))]

theorem simulateQ_probingHashImpl_ftsLeafHash_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (secret : Digest) :
    simulateQ (probingHashImpl parameter)
        (ftsLeafHash parameter index tree leafIdx secret) =
      simulateQ ordinaryHashImpl
        (ftsLeafHash parameter index tree leafIdx secret) := by
  unfold ftsLeafHash
  exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
    (.ftsLeaf index tree leafIdx) (digestBytes secret) (by trivial)
      (by simp) (by simp) (by simp)

theorem simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (path : Fin ftsTreeHeight → Digest) :
    ∀ levels value, levels ≤ ftsTreeHeight →
      simulateQ (probingHashImpl parameter)
          (ftsFold parameter index tree leafIdx path levels value) =
        simulateQ ordinaryHashImpl
          (ftsFold parameter index tree leafIdx path levels value)
  | 0, value, _ => by simp [ftsFold]
  | levels + 1, value, hlevels => by
      rw [ftsFold_succ_eq, simulateQ_bind, simulateQ_bind,
        simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl parameter index tree
          leafIdx path levels value (by omega)]
      apply bind_congr
      intro current
      split <;> split <;>
        exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
          (.ftsNode index tree (levels + 1) (leafIdx.val / 2 ^ (levels + 1))) _
            (by
              show levels + 1 < 2 ^ 32 ∧ leafIdx.val / 2 ^ (levels + 1) < 2 ^ 32
              constructor
              · have hheight : ftsTreeHeight < 2 ^ 32 := by
                  norm_num [ftsTreeHeight]
                omega
              · have hleaf : leafIdx.val < 2 ^ 32 := by
                  exact lt_of_lt_of_le leafIdx.isLt (by norm_num [ftsTreeHeight])
                have hdiv := Nat.div_le_self leafIdx.val (2 ^ (levels + 1))
                omega)
            (by simp) (by simp) (by simp)

theorem simulateQ_probingHashImpl_sequenceFin_eq_ordinaryHashImpl
    (parameter : PublicParameter) {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomponent : ∀ position,
      simulateQ (probingHashImpl parameter) (computation position) =
        simulateQ ordinaryHashImpl (computation position)) :
    simulateQ (probingHashImpl parameter) (sequenceFin computation) =
      simulateQ ordinaryHashImpl (sequenceFin computation) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind, simulateQ_bind, hcomponent 0]
      apply bind_congr
      intro head
      rw [simulateQ_bind, simulateQ_bind]
      have htail := ih (fun position : Fin n => computation position.succ)
        (fun position => hcomponent position.succ)
      rw [htail]
      simp only [simulateQ_pure]

theorem simulateQ_probingHashImpl_ftsRecover_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    simulateQ (probingHashImpl parameter)
        (ftsRecover parameter index leaves secrets paths) =
      simulateQ ordinaryHashImpl
        (ftsRecover parameter index leaves secrets paths) := by
  unfold ftsRecover
  rw [simulateQ_bind, simulateQ_bind]
  have hroots := simulateQ_probingHashImpl_sequenceFin_eq_ordinaryHashImpl parameter
    (fun tree => do
      let leaf := leaves (ftsIndexOf tree)
      let value ← ftsLeafHash parameter index tree leaf (secrets tree)
      ftsFold parameter index tree leaf (paths tree) ftsTreeHeight value)
    (fun tree => by
      rw [simulateQ_bind, simulateQ_bind,
        simulateQ_probingHashImpl_ftsLeafHash_eq_ordinaryHashImpl]
      apply bind_congr
      intro value
      exact simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl parameter index tree
        (leaves (ftsIndexOf tree)) (paths tree) ftsTreeHeight value le_rfl)
  rw [hroots]
  apply bind_congr
  intro roots
  exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
    (.ftsRoots index) (ftsRootsPayload roots) (by trivial)
      (by simp) (by simp) (by simp)

theorem simulateQ_verifierHashImpl_tweakableHash_eq_ordinaryHashImpl
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hchain : ∀ lay tree leafIdx chainIdx step,
      domain ≠ .chain lay tree leafIdx chainIdx step)
    (hleaf : ∀ lay tree leafIdx, domain ≠ .leaf lay tree leafIdx)
    (hnode : ∀ lay tree level nodeIdx, domain ≠ .node lay tree level nodeIdx) :
    simulateQ (verifierHashImpl parameter) (tweakableHash parameter domain payload) =
      simulateQ ordinaryHashImpl (tweakableHash parameter domain payload) := by
  unfold tweakableHash oracleHash
  rw [simulateQ_bind, simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query, simulateQ_pure]
  change (verifierHashQuery parameter (tweakableHashInput parameter domain payload) >>= _) = _
  rw [verifierHashQuery_eq_splitHashQuery_of_stable parameter _
    (stableOrdinaryInput_tweakableHashInput parameter domain payload hinRange
      hchain hleaf hnode)]
  rfl

theorem simulateQ_verifierHashImpl_messageDigest_eq_ordinaryHashImpl
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    simulateQ (verifierHashImpl parameter)
        (messageDigest parameter root message randomness) =
      simulateQ ordinaryHashImpl
        (messageDigest parameter root message randomness) := by
  unfold messageDigest oracleHash
  rw [simulateQ_bind, simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query, simulateQ_pure]
  change (verifierHashQuery parameter
    (tweakableHashInput parameter .message _) >>= _) = _
  rw [verifierHashQuery_eq_splitHashQuery_of_stable parameter _
    (stableOrdinaryInput_tweakableHashInput parameter .message _ (by trivial)
      (by simp) (by simp) (by simp))]
  rfl

theorem simulateQ_verifierHashImpl_ftsLeafHash_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (secret : Digest) :
    simulateQ (verifierHashImpl parameter)
        (ftsLeafHash parameter index tree leafIdx secret) =
      simulateQ ordinaryHashImpl
        (ftsLeafHash parameter index tree leafIdx secret) := by
  unfold ftsLeafHash
  exact simulateQ_verifierHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
    (.ftsLeaf index tree leafIdx) (digestBytes secret) (by trivial)
      (by simp) (by simp) (by simp)

theorem simulateQ_verifierHashImpl_ftsFold_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (path : Fin ftsTreeHeight → Digest) :
    ∀ levels value, levels ≤ ftsTreeHeight →
      simulateQ (verifierHashImpl parameter)
          (ftsFold parameter index tree leafIdx path levels value) =
        simulateQ ordinaryHashImpl
          (ftsFold parameter index tree leafIdx path levels value)
  | 0, value, _ => by simp [ftsFold]
  | levels + 1, value, hlevels => by
      rw [ftsFold_succ_eq, simulateQ_bind, simulateQ_bind,
        simulateQ_verifierHashImpl_ftsFold_eq_ordinaryHashImpl parameter index tree
          leafIdx path levels value (by omega)]
      apply bind_congr
      intro current
      split <;> split <;>
        exact simulateQ_verifierHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
          (.ftsNode index tree (levels + 1) (leafIdx.val / 2 ^ (levels + 1))) _
            (by
              show levels + 1 < 2 ^ 32 ∧ leafIdx.val / 2 ^ (levels + 1) < 2 ^ 32
              constructor
              · have hheight : ftsTreeHeight < 2 ^ 32 := by
                  norm_num [ftsTreeHeight]
                omega
              · have hleaf : leafIdx.val < 2 ^ 32 := by
                  exact lt_of_lt_of_le leafIdx.isLt (by norm_num [ftsTreeHeight])
                have hdiv := Nat.div_le_self leafIdx.val (2 ^ (levels + 1))
                omega)
            (by simp) (by simp) (by simp)

theorem simulateQ_verifierHashImpl_sequenceFin_eq_ordinaryHashImpl
    (parameter : PublicParameter) {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomponent : ∀ position,
      simulateQ (verifierHashImpl parameter) (computation position) =
        simulateQ ordinaryHashImpl (computation position)) :
    simulateQ (verifierHashImpl parameter) (sequenceFin computation) =
      simulateQ ordinaryHashImpl (sequenceFin computation) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind, simulateQ_bind, hcomponent 0]
      apply bind_congr
      intro head
      rw [simulateQ_bind, simulateQ_bind]
      have htail := ih (fun position : Fin n => computation position.succ)
        (fun position => hcomponent position.succ)
      rw [htail]
      simp only [simulateQ_pure]

theorem simulateQ_verifierHashImpl_ftsRecover_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    simulateQ (verifierHashImpl parameter)
        (ftsRecover parameter index leaves secrets paths) =
      simulateQ ordinaryHashImpl
        (ftsRecover parameter index leaves secrets paths) := by
  unfold ftsRecover
  rw [simulateQ_bind, simulateQ_bind]
  have hroots := simulateQ_verifierHashImpl_sequenceFin_eq_ordinaryHashImpl parameter
    (fun tree => do
      let leaf := leaves (ftsIndexOf tree)
      let value ← ftsLeafHash parameter index tree leaf (secrets tree)
      ftsFold parameter index tree leaf (paths tree) ftsTreeHeight value)
    (fun tree => by
      rw [simulateQ_bind, simulateQ_bind,
        simulateQ_verifierHashImpl_ftsLeafHash_eq_ordinaryHashImpl]
      apply bind_congr
      intro value
      exact simulateQ_verifierHashImpl_ftsFold_eq_ordinaryHashImpl parameter index tree
        (leaves (ftsIndexOf tree)) (paths tree) ftsTreeHeight value le_rfl)
  rw [hroots]
  apply bind_congr
  intro roots
  exact simulateQ_verifierHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
    (.ftsRoots index) (ftsRootsPayload roots) (by trivial)
      (by simp) (by simp) (by simp)

set_option maxRecDepth 10000 in
theorem ChainInvariant.not_finalized_false_of_bottom_verifyProbe_verifier
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {table : Coordinate → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {targetCache : QueryCache HashSpec}
    {initialState rawState completedState : LazyRevealProbe.State Coordinate}
    {initialCache rawCache : SplitHashCache} {root : Digest} {forgery : Forgery}
    {signingLog : QueryLog SigningSpec} {fuel remaining : Nat} {verified : Bool}
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      initialState initialCache)
    (hf : CacheAnswersAgreeOnRun (ordinaryQueryCache rawCache) f
      (verify ⟨root, parameter⟩ forgery.message forgery.signature))
    (hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hverify : LazyRevealProbe.RawResult.done rawState remaining
        (verified, rawCache) ∈ support
      (LazyRevealProbe.runRaw initialState fuel
        ((simulateQ (verifierRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
            initialCache)))
    (hprobe : VerifyProbeWitnessAt f targetCache
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature bottomLayer) : False := by
  obtain ⟨digest, layerMessage, codeword, chainIdx, hdigit, probe, input, hinput,
    hdigest, hadmissible, hencode, hverifierMessage, hhits, hmatches, _, _,
    hnotCovered⟩ := hprobe
  have hlayerMessage := VerifierLayerMessage.bottom_message hverifierMessage
  rw [hlayerMessage] at hencode
  have hchain := probe.isChainCoordinate_of_matchesInput hmatches
  have hcandidate : probe.candidate = truncateHash (table probe.coordinate) :=
    hhits.trans (probe.target_eq_truncate_table_of_chain f parameter table ftsSecret hchain
      hrealizes)
  have hinitialValue := hinvariant.1.value_eq_none_of_not_allowed hchain hnotCovered
  have hinitialNotRevealed := hinvariant.1.not_revealed_of_not_allowed hchain hnotCovered
  have hrawTable : ∀ coordinate output, rawState.values coordinate = some output →
      output = table coordinate := by
    intro coordinate output hvalue
    exact hcompletedTable coordinate output
      (finalizeDetailedFrom_preserves_value rawState.coordinates.toList rawState completedState
        coordinate output hvalue hfinalize)
  rw [simulateQ_verifierRom_scheme_verify, verify_eq, simulateQ_bind,
    StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hverify
  obtain ⟨digestRaw, hdigestRaw, hafterDigest⟩ := hverify
  cases digestRaw with
  | stopped hit => simp at hafterDigest
  | done digestState digestRemaining digestResult =>
      rcases digestResult with ⟨sampledDigest, digestCache⟩
      have hfDigest : CacheAnswersAgreeOnRun (ordinaryQueryCache digestCache) f
          (messageDigest parameter root forgery.message forgery.signature.randomness) := by
        intro query hquery output hcached
        apply hf query
        · rw [verify_eq, queriedInputs_bind]
          exact List.mem_append_left _ hquery
        · exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
            digestState digestCache digestRemaining rawState remaining verified rawCache output
              hcached hafterDigest
      have hdigestEval :=
        (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
        (messageDigest parameter root forgery.message forgery.signature.randomness)
          initialState digestState initialCache digestCache fuel digestRemaining sampledDigest
            hfDigest hdigestRaw).1
      rw [hdigest] at hdigestEval
      subst sampledDigest
      have hdigestOrdinary := hdigestRaw
      rw [simulateQ_verifierHashImpl_messageDigest_eq_ordinaryHashImpl] at hdigestOrdinary
      have hdigestState := mem_runRaw_simulateQ_ordinaryHashImpl_projects
        (messageDigest parameter root forgery.message forgery.signature.randomness)
          initialState digestState initialCache digestCache fuel digestRemaining digest
            hdigestOrdinary
      simp only [hadmissible, not_true_eq_false, ↓reduceIte] at hafterDigest
      rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hafterDigest
      obtain ⟨ftsRaw, hftsRaw, hafterFts⟩ := hafterDigest
      cases ftsRaw with
      | stopped hit => simp at hafterFts
      | done ftsState ftsRemaining ftsResult =>
          rcases ftsResult with ⟨ftsPublicKey, ftsCache⟩
          have hfFts : CacheAnswersAgreeOnRun (ordinaryQueryCache ftsCache) f
              (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                forgery.signature.ftsSecret forgery.signature.ftsPath) := by
            intro query hquery output hcached
            apply hf query
            · rw [verify_eq, queriedInputs_bind]
              apply List.mem_append_right
              rw [hdigest]
              simp only [hadmissible, not_true_eq_false, if_false, queriedInputs_bind]
              exact List.mem_append_left _ hquery
            · exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                ftsState ftsCache ftsRemaining rawState remaining verified rawCache output hcached
                  hafterFts
          have hftsEval :=
            (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
              forgery.signature.ftsSecret forgery.signature.ftsPath)
            digestState ftsState digestCache ftsCache digestRemaining ftsRemaining ftsPublicKey
              hfFts hftsRaw).1
          have hftsOrdinary := hftsRaw
          rw [simulateQ_verifierHashImpl_ftsRecover_eq_ordinaryHashImpl] at hftsOrdinary
          have hftsState := mem_runRaw_simulateQ_ordinaryHashImpl_projects
            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
              forgery.signature.ftsSecret forgery.signature.ftsPath)
            digestState ftsState digestCache ftsCache digestRemaining ftsRemaining ftsPublicKey
              hftsOrdinary
          subst ftsPublicKey
          simp only at hafterFts
          rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterFts
          obtain ⟨layersRaw, hlayersRaw, hafterLayers⟩ := hafterFts
          cases layersRaw with
          | stopped hit => simp at hafterLayers
          | done layersState layersRemaining layersResult =>
              rcases layersResult with ⟨verifiedRoot, layersCache⟩
              rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
                dif_pos bottomLayer.isLt, simulateQ_bind, StateT.run_bind,
                LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hlayersRaw
              obtain ⟨otsRaw, hotsRaw, hafterOts⟩ := hlayersRaw
              cases otsRaw with
              | stopped hit => simp at hafterOts
              | done otsState otsRemaining otsResult =>
                  rcases otsResult with ⟨leafResult, otsCache⟩
                  have hfOts : CacheAnswersAgreeOnRun (ordinaryQueryCache otsCache) f
                      (encode parameter bottomLayer
                        (treeIndexAt (digestIndex digest) bottomLayer)
                        (leafIndexAt (digestIndex digest) bottomLayer)
                        (evalWithAnswerFn f
                          (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                            forgery.signature.ftsSecret forgery.signature.ftsPath))
                        (forgery.signature.counter bottomLayer)) := by
                    intro query hquery output hcached
                    apply hf query
                    · exact VerifierLayerMessage.otsLeaf_query_mem_verify
                        (publicKey := ⟨root, parameter⟩) (message := forgery.message)
                        (signature := forgery.signature) hdigest hadmissible hverifierMessage
                          (by
                            unfold otsLeaf
                            rw [queriedInputs_bind]
                            exact List.mem_append_left _
                              (by simpa only [hlayerMessage] using hquery))
                    · have hcachedLayers :=
                        (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                          otsState otsCache otsRemaining layersState layersRemaining verifiedRoot
                            layersCache output hcached hafterOts
                      exact
                        (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                          layersState layersCache layersRemaining rawState remaining verified
                            rawCache output hcachedLayers hafterLayers
                  have hvaluesOtsLayers := LazyRevealProbe.valuesLE_of_mem_runRaw_done _ otsState
                    layersState otsRemaining layersRemaining (verifiedRoot, layersCache) hafterOts
                  have hvaluesLayersRaw := LazyRevealProbe.valuesLE_of_mem_runRaw_done _ layersState
                    rawState layersRemaining remaining (verified, rawCache) hafterLayers
                  have htableOts : ∀ coordinate output,
                      otsState.values coordinate = some output → output = table coordinate := by
                    intro coordinate output hvalue
                    exact hrawTable coordinate output
                      (hvaluesLayersRaw coordinate output
                        (hvaluesOtsLayers coordinate output hvalue))
                  rw [hinput] at hmatches
                  have hftsInitial : ftsState = initialState :=
                    hftsState.1.trans hdigestState.1
                  have hpendingOts :=
                    simulateQ_verifierHashImpl_otsLeaf_pendingHit_of_correct_probe f parameter
                      table probe bottomLayer (treeIndexAt (digestIndex digest) bottomLayer)
                        (leafIndexAt (digestIndex digest) bottomLayer)
                        (evalWithAnswerFn f
                          (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                            forgery.signature.ftsSecret forgery.signature.ftsPath))
                        (forgery.signature.counter bottomLayer)
                        (forgery.signature.chainValue bottomLayer) codeword chainIdx hdigit hencode
                          ftsState otsState ftsCache otsCache ftsRemaining otsRemaining leafResult
                            hmatches hcandidate (by simpa [hftsInitial] using hinitialValue)
                            (by simpa [hftsInitial] using hinitialNotRevealed) hfOts htableOts
                              hotsRaw
                  have htableLayers : ∀ output,
                      layersState.values probe.coordinate = some output →
                        output = table probe.coordinate := by
                    intro output hvalue
                    exact hrawTable probe.coordinate output
                      (hvaluesLayersRaw probe.coordinate output hvalue)
                  have hpendingLayers := LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done _
                    probe.coordinate (table probe.coordinate) otsState layersState otsRemaining
                      layersRemaining (verifiedRoot, layersCache) hpendingOts.1 hpendingOts.2
                        htableLayers hafterOts
                  have hpendingRaw := LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done _
                    probe.coordinate (table probe.coordinate) layersState rawState layersRemaining
                      remaining (verified, rawCache) hpendingLayers.1 hpendingLayers.2
                        (hrawTable probe.coordinate) hafterLayers
                  exact finalizeDetailed_false_of_pending_hit table rawState completedState
                    probe.coordinate hpendingRaw.1 hpendingRaw.2
                      (hcompletedTable probe.coordinate) hfinalize

set_option maxRecDepth 10000 in
theorem ChainInvariant.not_finalized_false_of_middle_verifyProbe_verifier
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {table : Coordinate → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {targetCache : QueryCache HashSpec}
    {initialState rawState completedState : LazyRevealProbe.State Coordinate}
    {initialCache rawCache : SplitHashCache} {root : Digest} {forgery : Forgery}
    {signingLog : QueryLog SigningSpec} {fuel remaining : Nat} {verified : Bool}
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      initialState initialCache)
    (hf : CacheAnswersAgreeOnRun (ordinaryQueryCache rawCache) f
      (verify ⟨root, parameter⟩ forgery.message forgery.signature))
    (hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hverify : LazyRevealProbe.RawResult.done rawState remaining
        (verified, rawCache) ∈ support
      (LazyRevealProbe.runRaw initialState fuel
        ((simulateQ (verifierRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
            initialCache)))
    (hprobe : VerifyProbeWitnessAt f targetCache
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature middleLayer) : False := by
  obtain ⟨digest, layerMessage, codeword, chainIdx, hdigit, probe, input, hinput,
    hdigest, hadmissible, hencode, hverifierMessage, hhits, hmatches, _, _,
    hnotCovered⟩ := hprobe
  obtain ⟨bottomLeaf, hbottomLeaf, hlayerMessage⟩ :=
    VerifierLayerMessage.middle_data hverifierMessage
  rw [hinput] at hmatches
  have hchain := probe.isChainCoordinate_of_matchesInput hmatches
  have hcandidate : probe.candidate = truncateHash (table probe.coordinate) :=
    hhits.trans (probe.target_eq_truncate_table_of_chain f parameter table ftsSecret hchain
      hrealizes)
  have hinitialValue := hinvariant.1.value_eq_none_of_not_allowed hchain hnotCovered
  have hinitialNotRevealed := hinvariant.1.not_revealed_of_not_allowed hchain hnotCovered
  have hrawTable : ∀ coordinate output, rawState.values coordinate = some output →
      output = table coordinate := by
    intro coordinate output hvalue
    exact hcompletedTable coordinate output
      (finalizeDetailedFrom_preserves_value rawState.coordinates.toList rawState completedState
        coordinate output hvalue hfinalize)
  rw [simulateQ_verifierRom_scheme_verify, verify_eq, simulateQ_bind,
    StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hverify
  obtain ⟨digestRaw, hdigestRaw, hafterDigest⟩ := hverify
  cases digestRaw with
  | stopped hit => simp at hafterDigest
  | done digestState digestRemaining digestResult =>
      rcases digestResult with ⟨sampledDigest, digestCache⟩
      have hfDigest : CacheAnswersAgreeOnRun (ordinaryQueryCache digestCache) f
          (messageDigest parameter root forgery.message forgery.signature.randomness) := by
        intro query hquery output hcached
        apply hf query (messageDigest_query_mem_verify hquery)
        exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
          digestState digestCache digestRemaining rawState remaining verified rawCache output
            hcached hafterDigest
      have hdigestEval :=
        (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
        (messageDigest parameter root forgery.message forgery.signature.randomness)
          initialState digestState initialCache digestCache fuel digestRemaining sampledDigest
            hfDigest hdigestRaw).1
      rw [hdigest] at hdigestEval
      subst sampledDigest
      have hdigestOrdinary := hdigestRaw
      rw [simulateQ_verifierHashImpl_messageDigest_eq_ordinaryHashImpl] at hdigestOrdinary
      have hdigestState := mem_runRaw_simulateQ_ordinaryHashImpl_projects
        (messageDigest parameter root forgery.message forgery.signature.randomness)
          initialState digestState initialCache digestCache fuel digestRemaining digest
            hdigestOrdinary
      simp only [hadmissible, not_true_eq_false, ↓reduceIte] at hafterDigest
      rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hafterDigest
      obtain ⟨ftsRaw, hftsRaw, hafterFts⟩ := hafterDigest
      cases ftsRaw with
      | stopped hit => simp at hafterFts
      | done ftsState ftsRemaining ftsResult =>
          rcases ftsResult with ⟨ftsPublicKey, ftsCache⟩
          have hfFts : CacheAnswersAgreeOnRun (ordinaryQueryCache ftsCache) f
              (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                forgery.signature.ftsSecret forgery.signature.ftsPath) := by
            intro query hquery output hcached
            apply hf query (ftsRecover_query_mem_verify hdigest hadmissible hquery)
            exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
              ftsState ftsCache ftsRemaining rawState remaining verified rawCache output hcached
                hafterFts
          have hftsEval :=
            (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
              forgery.signature.ftsSecret forgery.signature.ftsPath)
            digestState ftsState digestCache ftsCache digestRemaining ftsRemaining ftsPublicKey
              hfFts hftsRaw).1
          have hftsOrdinary := hftsRaw
          rw [simulateQ_verifierHashImpl_ftsRecover_eq_ordinaryHashImpl] at hftsOrdinary
          have hftsState := mem_runRaw_simulateQ_ordinaryHashImpl_projects
            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
              forgery.signature.ftsSecret forgery.signature.ftsPath)
            digestState ftsState digestCache ftsCache digestRemaining ftsRemaining ftsPublicKey
              hftsOrdinary
          subst ftsPublicKey
          simp only at hafterFts
          rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterFts
          obtain ⟨layersRaw, hlayersRaw, hafterLayers⟩ := hafterFts
          cases layersRaw with
          | stopped hit => simp at hafterLayers
          | done layersState layersRemaining layersResult =>
              rcases layersResult with ⟨verifiedRoot, layersCache⟩
              rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
                dif_pos bottomLayer.isLt, simulateQ_bind, StateT.run_bind,
                LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hlayersRaw
              obtain ⟨bottomOtsRaw, hbottomOtsRaw, hafterBottomOts⟩ := hlayersRaw
              cases bottomOtsRaw with
              | stopped hit => simp at hafterBottomOts
              | done bottomOtsState bottomOtsRemaining bottomOtsResult =>
                  rcases bottomOtsResult with ⟨bottomResult, bottomOtsCache⟩
                  have hfBottomOts :
                      CacheAnswersAgreeOnRun (ordinaryQueryCache bottomOtsCache) f
                        (otsLeaf parameter bottomLayer
                          (treeIndexAt (digestIndex digest) bottomLayer)
                          (leafIndexAt (digestIndex digest) bottomLayer)
                          (evalWithAnswerFn f
                            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                              forgery.signature.ftsSecret forgery.signature.ftsPath))
                          (forgery.signature.counter bottomLayer)
                          (forgery.signature.chainValue bottomLayer)) := by
                    intro query hquery output hcached
                    apply hf query (bottomOts_query_mem_verify hdigest hadmissible hquery)
                    have hcachedLayers :=
                      (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                        bottomOtsState bottomOtsCache bottomOtsRemaining layersState
                          layersRemaining verifiedRoot layersCache output hcached hafterBottomOts
                    exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                      layersState layersCache layersRemaining rawState remaining verified rawCache
                        output hcachedLayers hafterLayers
                  have hbottomEval :=
                    (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
                    (otsLeaf parameter bottomLayer
                      (treeIndexAt (digestIndex digest) bottomLayer)
                      (leafIndexAt (digestIndex digest) bottomLayer)
                      (evalWithAnswerFn f
                        (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                          forgery.signature.ftsSecret forgery.signature.ftsPath))
                      (forgery.signature.counter bottomLayer)
                      (forgery.signature.chainValue bottomLayer))
                    ftsState bottomOtsState ftsCache bottomOtsCache ftsRemaining
                      bottomOtsRemaining bottomResult hfBottomOts hbottomOtsRaw).1
                  rw [hbottomLeaf] at hbottomEval
                  subst bottomResult
                  have hbottomOtsCoordinate :=
                    preservesCoordinate_simulateQ_verifierHashImpl_otsLeaf_of_layer_ne parameter
                      probe middleLayer (treeIndexAt (digestIndex digest) middleLayer)
                        (leafIndexAt (digestIndex digest) middleLayer) chainIdx
                        ⟨(codeword chainIdx).val, hdigit⟩
                        (forgery.signature.chainValue middleLayer chainIdx) hmatches bottomLayer
                        (treeIndexAt (digestIndex digest) bottomLayer)
                        (leafIndexAt (digestIndex digest) bottomLayer)
                        (evalWithAnswerFn f
                          (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                            forgery.signature.ftsSecret forgery.signature.ftsPath))
                        (forgery.signature.counter bottomLayer)
                        (forgery.signature.chainValue bottomLayer) (by decide)
                        ftsState ftsCache ftsRemaining bottomOtsState bottomOtsRemaining
                          (some bottomLeaf) bottomOtsCache hbottomOtsRaw
                  simp only at hafterBottomOts
                  rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
                    mem_support_bind_iff] at hafterBottomOts
                  obtain ⟨bottomFoldRaw, hbottomFoldRaw, hafterBottomFold⟩ := hafterBottomOts
                  cases bottomFoldRaw with
                  | stopped hit => simp at hafterBottomFold
                  | done bottomFoldState bottomFoldRemaining bottomFoldResult =>
                      rcases bottomFoldResult with ⟨bottomRoot, bottomFoldCache⟩
                      have hfBottomFold :
                          CacheAnswersAgreeOnRun (ordinaryQueryCache bottomFoldCache) f
                            (treeFold parameter bottomLayer
                              (treeIndexAt (digestIndex digest) bottomLayer)
                              (leafIndexAt (digestIndex digest) bottomLayer)
                              (signaturePath forgery.signature bottomLayer)
                              (layerHeight bottomLayer) bottomLeaf) := by
                        intro query hquery output hcached
                        apply hf query
                          (bottomFold_query_mem_verify hdigest hadmissible hbottomLeaf hquery)
                        have hcachedLayers :=
                          (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                            bottomFoldState bottomFoldCache bottomFoldRemaining layersState
                              layersRemaining verifiedRoot layersCache output hcached
                                hafterBottomFold
                        exact
                          (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                            layersState layersCache layersRemaining rawState remaining verified
                              rawCache output hcachedLayers hafterLayers
                      have hbottomFoldEval :=
                        (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
                          (treeFold parameter bottomLayer
                            (treeIndexAt (digestIndex digest) bottomLayer)
                            (leafIndexAt (digestIndex digest) bottomLayer)
                            (signaturePath forgery.signature bottomLayer)
                            (layerHeight bottomLayer) bottomLeaf)
                          bottomOtsState bottomFoldState bottomOtsCache bottomFoldCache
                            bottomOtsRemaining bottomFoldRemaining bottomRoot hfBottomFold
                              hbottomFoldRaw).1
                      change foldValue f parameter bottomLayer
                        (treeIndexAt (digestIndex digest) bottomLayer)
                        (leafIndexAt (digestIndex digest) bottomLayer)
                        (signaturePath forgery.signature bottomLayer) bottomLeaf
                          (layerHeight bottomLayer) = bottomRoot at hbottomFoldEval
                      rw [← hlayerMessage] at hbottomFoldEval
                      subst bottomRoot
                      have hbottomFoldCoordinate :=
                        preservesCoordinate_simulateQ_verifierHashImpl_treeFold_of_layer_ne
                          parameter probe middleLayer
                          (treeIndexAt (digestIndex digest) middleLayer)
                          (leafIndexAt (digestIndex digest) middleLayer) chainIdx
                          ⟨(codeword chainIdx).val, hdigit⟩
                          (forgery.signature.chainValue middleLayer chainIdx) hmatches bottomLayer
                          (treeIndexAt (digestIndex digest) bottomLayer)
                          (leafIndexAt (digestIndex digest) bottomLayer)
                          (signaturePath forgery.signature bottomLayer) (by decide)
                          (layerHeight bottomLayer) bottomLeaf (layerHeight_le bottomLayer)
                          bottomOtsState bottomOtsCache bottomOtsRemaining bottomFoldState
                            bottomFoldRemaining layerMessage bottomFoldCache hbottomFoldRaw
                      simp only at hafterBottomFold
                      rw [show bottomLayer.val = middleLayer.val + 1 by rfl,
                        verifyLayers_succ_eq, dif_pos middleLayer.isLt, simulateQ_bind,
                        StateT.run_bind, LazyRevealProbe.runRaw_bind,
                        mem_support_bind_iff] at hafterBottomFold
                      obtain ⟨middleOtsRaw, hmiddleOtsRaw, hafterMiddleOts⟩ :=
                        hafterBottomFold
                      cases middleOtsRaw with
                      | stopped hit => simp at hafterMiddleOts
                      | done middleOtsState middleOtsRemaining middleOtsResult =>
                          rcases middleOtsResult with ⟨middleResult, middleOtsCache⟩
                          have hfMiddleOts :
                              CacheAnswersAgreeOnRun (ordinaryQueryCache middleOtsCache) f
                                (encode parameter middleLayer
                                  (treeIndexAt (digestIndex digest) middleLayer)
                                  (leafIndexAt (digestIndex digest) middleLayer) layerMessage
                                  (forgery.signature.counter middleLayer)) := by
                            intro query hquery output hcached
                            apply hf query
                              (VerifierLayerMessage.otsLeaf_query_mem_verify hdigest hadmissible
                                hverifierMessage (by
                                  unfold otsLeaf
                                  rw [queriedInputs_bind]
                                  exact List.mem_append_left _ hquery))
                            have hcachedLayers :=
                              (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                                middleOtsState middleOtsCache middleOtsRemaining layersState
                                  layersRemaining verifiedRoot layersCache output hcached
                                    hafterMiddleOts
                            exact
                              (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                                layersState layersCache layersRemaining rawState remaining verified
                                  rawCache output hcachedLayers hafterLayers
                          have hvaluesMiddleLayers :=
                            LazyRevealProbe.valuesLE_of_mem_runRaw_done _ middleOtsState
                              layersState middleOtsRemaining layersRemaining
                                (verifiedRoot, layersCache) hafterMiddleOts
                          have hvaluesLayersRaw :=
                            LazyRevealProbe.valuesLE_of_mem_runRaw_done _ layersState rawState
                              layersRemaining remaining (verified, rawCache) hafterLayers
                          have htableMiddle : ∀ coordinate output,
                              middleOtsState.values coordinate = some output →
                                output = table coordinate := by
                            intro coordinate output hvalue
                            exact hrawTable coordinate output
                              (hvaluesLayersRaw coordinate output
                                (hvaluesMiddleLayers coordinate output hvalue))
                          have hftsInitial : ftsState = initialState :=
                            hftsState.1.trans hdigestState.1
                          have hmiddleInitialValue :
                              bottomFoldState.values probe.coordinate = none := by
                            rw [hbottomFoldCoordinate.1, hbottomOtsCoordinate.1, hftsInitial,
                              hinitialValue]
                          have hmiddleInitialNotRevealed :
                              probe.coordinate ∉ bottomFoldState.revealed := by
                            rw [hbottomFoldCoordinate.2, hbottomOtsCoordinate.2, hftsInitial]
                            exact hinitialNotRevealed
                          have hpendingMiddle :=
                            simulateQ_verifierHashImpl_otsLeaf_pendingHit_of_correct_probe f
                              parameter table probe middleLayer
                                (treeIndexAt (digestIndex digest) middleLayer)
                                (leafIndexAt (digestIndex digest) middleLayer) layerMessage
                                (forgery.signature.counter middleLayer)
                                (forgery.signature.chainValue middleLayer) codeword chainIdx hdigit
                                hencode bottomFoldState middleOtsState bottomFoldCache
                                middleOtsCache bottomFoldRemaining middleOtsRemaining middleResult
                                hmatches hcandidate hmiddleInitialValue hmiddleInitialNotRevealed
                                hfMiddleOts htableMiddle hmiddleOtsRaw
                          have htableLayers : ∀ output,
                              layersState.values probe.coordinate = some output →
                                output = table probe.coordinate := by
                            intro output hvalue
                            exact hrawTable probe.coordinate output
                              (hvaluesLayersRaw probe.coordinate output hvalue)
                          have hpendingLayers :=
                            LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done _
                              probe.coordinate (table probe.coordinate) middleOtsState layersState
                              middleOtsRemaining layersRemaining (verifiedRoot, layersCache)
                              hpendingMiddle.1 hpendingMiddle.2 htableLayers hafterMiddleOts
                          have hpendingRaw :=
                            LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done _
                              probe.coordinate (table probe.coordinate) layersState rawState
                              layersRemaining remaining (verified, rawCache) hpendingLayers.1
                              hpendingLayers.2 (hrawTable probe.coordinate) hafterLayers
                          exact finalizeDetailed_false_of_pending_hit table rawState completedState
                            probe.coordinate hpendingRaw.1 hpendingRaw.2
                              (hcompletedTable probe.coordinate) hfinalize

set_option maxRecDepth 10000 in
theorem ChainInvariant.not_finalized_false_of_top_verifyProbe_verifier
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {table : Coordinate → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {targetCache : QueryCache HashSpec}
    {initialState rawState completedState : LazyRevealProbe.State Coordinate}
    {initialCache rawCache : SplitHashCache} {root : Digest} {forgery : Forgery}
    {signingLog : QueryLog SigningSpec} {fuel remaining : Nat} {verified : Bool}
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      initialState initialCache)
    (hf : CacheAnswersAgreeOnRun (ordinaryQueryCache rawCache) f
      (verify ⟨root, parameter⟩ forgery.message forgery.signature))
    (hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hverify : LazyRevealProbe.RawResult.done rawState remaining
        (verified, rawCache) ∈ support
      (LazyRevealProbe.runRaw initialState fuel
        ((simulateQ (verifierRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
            initialCache)))
    (hprobe : VerifyProbeWitnessAt f targetCache
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature topLayer) : False := by
  obtain ⟨digest, layerMessage, codeword, chainIdx, hdigit, probe, input, hinput,
    hdigest, hadmissible, hencode, hverifierMessage, hhits, hmatches, _, _,
    hnotCovered⟩ := hprobe
  obtain ⟨bottomLeaf, middleLeaf, hbottomLeaf, hmiddleLeaf, hlayerMessage⟩ :=
    VerifierLayerMessage.top_data hverifierMessage
  rw [hinput] at hmatches
  have hchain := probe.isChainCoordinate_of_matchesInput hmatches
  have hcandidate : probe.candidate = truncateHash (table probe.coordinate) :=
    hhits.trans (probe.target_eq_truncate_table_of_chain f parameter table ftsSecret hchain
      hrealizes)
  have hinitialValue := hinvariant.1.value_eq_none_of_not_allowed hchain hnotCovered
  have hinitialNotRevealed := hinvariant.1.not_revealed_of_not_allowed hchain hnotCovered
  have hrawTable : ∀ coordinate output, rawState.values coordinate = some output →
      output = table coordinate := by
    intro coordinate output hvalue
    exact hcompletedTable coordinate output
      (finalizeDetailedFrom_preserves_value rawState.coordinates.toList rawState completedState
        coordinate output hvalue hfinalize)
  rw [simulateQ_verifierRom_scheme_verify, verify_eq, simulateQ_bind,
    StateT.run_bind, LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hverify
  obtain ⟨digestRaw, hdigestRaw, hafterDigest⟩ := hverify
  cases digestRaw with
  | stopped hit => simp at hafterDigest
  | done digestState digestRemaining digestResult =>
      rcases digestResult with ⟨sampledDigest, digestCache⟩
      have hfDigest : CacheAnswersAgreeOnRun (ordinaryQueryCache digestCache) f
          (messageDigest parameter root forgery.message forgery.signature.randomness) := by
        intro query hquery output hcached
        apply hf query (messageDigest_query_mem_verify hquery)
        exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
          digestState digestCache digestRemaining rawState remaining verified rawCache output
            hcached hafterDigest
      have hdigestEval :=
        (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
        (messageDigest parameter root forgery.message forgery.signature.randomness)
          initialState digestState initialCache digestCache fuel digestRemaining sampledDigest
            hfDigest hdigestRaw).1
      rw [hdigest] at hdigestEval
      subst sampledDigest
      have hdigestOrdinary := hdigestRaw
      rw [simulateQ_verifierHashImpl_messageDigest_eq_ordinaryHashImpl] at hdigestOrdinary
      have hdigestState := mem_runRaw_simulateQ_ordinaryHashImpl_projects
        (messageDigest parameter root forgery.message forgery.signature.randomness)
          initialState digestState initialCache digestCache fuel digestRemaining digest
            hdigestOrdinary
      simp only [hadmissible, not_true_eq_false, ↓reduceIte] at hafterDigest
      rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hafterDigest
      obtain ⟨ftsRaw, hftsRaw, hafterFts⟩ := hafterDigest
      cases ftsRaw with
      | stopped hit => simp at hafterFts
      | done ftsState ftsRemaining ftsResult =>
          rcases ftsResult with ⟨ftsPublicKey, ftsCache⟩
          have hfFts : CacheAnswersAgreeOnRun (ordinaryQueryCache ftsCache) f
              (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                forgery.signature.ftsSecret forgery.signature.ftsPath) := by
            intro query hquery output hcached
            apply hf query (ftsRecover_query_mem_verify hdigest hadmissible hquery)
            exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
              ftsState ftsCache ftsRemaining rawState remaining verified rawCache output hcached
                hafterFts
          have hftsEval :=
            (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
              forgery.signature.ftsSecret forgery.signature.ftsPath)
            digestState ftsState digestCache ftsCache digestRemaining ftsRemaining ftsPublicKey
              hfFts hftsRaw).1
          have hftsOrdinary := hftsRaw
          rw [simulateQ_verifierHashImpl_ftsRecover_eq_ordinaryHashImpl] at hftsOrdinary
          have hftsState := mem_runRaw_simulateQ_ordinaryHashImpl_projects
            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
              forgery.signature.ftsSecret forgery.signature.ftsPath)
            digestState ftsState digestCache ftsCache digestRemaining ftsRemaining ftsPublicKey
              hftsOrdinary
          subst ftsPublicKey
          simp only at hafterFts
          rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
            mem_support_bind_iff] at hafterFts
          obtain ⟨layersRaw, hlayersRaw, hafterLayers⟩ := hafterFts
          cases layersRaw with
          | stopped hit => simp at hafterLayers
          | done layersState layersRemaining layersResult =>
              rcases layersResult with ⟨verifiedRoot, layersCache⟩
              rw [show numLayers = bottomLayer.val + 1 by rfl, verifyLayers_succ_eq,
                dif_pos bottomLayer.isLt, simulateQ_bind, StateT.run_bind,
                LazyRevealProbe.runRaw_bind, mem_support_bind_iff] at hlayersRaw
              obtain ⟨bottomOtsRaw, hbottomOtsRaw, hafterBottomOts⟩ := hlayersRaw
              cases bottomOtsRaw with
              | stopped hit => simp at hafterBottomOts
              | done bottomOtsState bottomOtsRemaining bottomOtsResult =>
                  rcases bottomOtsResult with ⟨bottomResult, bottomOtsCache⟩
                  have hfBottomOts :
                      CacheAnswersAgreeOnRun (ordinaryQueryCache bottomOtsCache) f
                        (otsLeaf parameter bottomLayer
                          (treeIndexAt (digestIndex digest) bottomLayer)
                          (leafIndexAt (digestIndex digest) bottomLayer)
                          (evalWithAnswerFn f
                            (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                              forgery.signature.ftsSecret forgery.signature.ftsPath))
                          (forgery.signature.counter bottomLayer)
                          (forgery.signature.chainValue bottomLayer)) := by
                    intro query hquery output hcached
                    apply hf query (bottomOts_query_mem_verify hdigest hadmissible hquery)
                    have hcachedLayers :=
                      (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                        bottomOtsState bottomOtsCache bottomOtsRemaining layersState
                          layersRemaining verifiedRoot layersCache output hcached hafterBottomOts
                    exact (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                      layersState layersCache layersRemaining rawState remaining verified rawCache
                        output hcachedLayers hafterLayers
                  have hbottomEval :=
                    (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
                    (otsLeaf parameter bottomLayer
                      (treeIndexAt (digestIndex digest) bottomLayer)
                      (leafIndexAt (digestIndex digest) bottomLayer)
                      (evalWithAnswerFn f
                        (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                          forgery.signature.ftsSecret forgery.signature.ftsPath))
                      (forgery.signature.counter bottomLayer)
                      (forgery.signature.chainValue bottomLayer))
                    ftsState bottomOtsState ftsCache bottomOtsCache ftsRemaining
                      bottomOtsRemaining bottomResult hfBottomOts hbottomOtsRaw).1
                  rw [hbottomLeaf] at hbottomEval
                  subst bottomResult
                  have hbottomOtsCoordinate :=
                    preservesCoordinate_simulateQ_verifierHashImpl_otsLeaf_of_layer_ne parameter
                      probe topLayer (treeIndexAt (digestIndex digest) topLayer)
                        (leafIndexAt (digestIndex digest) topLayer) chainIdx
                        ⟨(codeword chainIdx).val, hdigit⟩
                        (forgery.signature.chainValue topLayer chainIdx) hmatches bottomLayer
                        (treeIndexAt (digestIndex digest) bottomLayer)
                        (leafIndexAt (digestIndex digest) bottomLayer)
                        (evalWithAnswerFn f
                          (ftsRecover parameter (digestIndex digest) (digestLeaves digest)
                            forgery.signature.ftsSecret forgery.signature.ftsPath))
                        (forgery.signature.counter bottomLayer)
                        (forgery.signature.chainValue bottomLayer) (by decide)
                        ftsState ftsCache ftsRemaining bottomOtsState bottomOtsRemaining
                          (some bottomLeaf) bottomOtsCache hbottomOtsRaw
                  simp only at hafterBottomOts
                  rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
                    mem_support_bind_iff] at hafterBottomOts
                  obtain ⟨bottomFoldRaw, hbottomFoldRaw, hafterBottomFold⟩ := hafterBottomOts
                  cases bottomFoldRaw with
                  | stopped hit => simp at hafterBottomFold
                  | done bottomFoldState bottomFoldRemaining bottomFoldResult =>
                      rcases bottomFoldResult with ⟨bottomRoot, bottomFoldCache⟩
                      have hfBottomFold :
                          CacheAnswersAgreeOnRun (ordinaryQueryCache bottomFoldCache) f
                            (treeFold parameter bottomLayer
                              (treeIndexAt (digestIndex digest) bottomLayer)
                              (leafIndexAt (digestIndex digest) bottomLayer)
                              (signaturePath forgery.signature bottomLayer)
                              (layerHeight bottomLayer) bottomLeaf) := by
                        intro query hquery output hcached
                        apply hf query
                          (bottomFold_query_mem_verify hdigest hadmissible hbottomLeaf hquery)
                        have hcachedLayers :=
                          (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                            bottomFoldState bottomFoldCache bottomFoldRemaining layersState
                              layersRemaining verifiedRoot layersCache output hcached
                                hafterBottomFold
                        exact
                          (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                            layersState layersCache layersRemaining rawState remaining verified
                              rawCache output hcachedLayers hafterLayers
                      have hbottomFoldEval :=
                        (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f parameter
                          (treeFold parameter bottomLayer
                            (treeIndexAt (digestIndex digest) bottomLayer)
                            (leafIndexAt (digestIndex digest) bottomLayer)
                            (signaturePath forgery.signature bottomLayer)
                            (layerHeight bottomLayer) bottomLeaf)
                          bottomOtsState bottomFoldState bottomOtsCache bottomFoldCache
                            bottomOtsRemaining bottomFoldRemaining bottomRoot hfBottomFold
                              hbottomFoldRaw).1
                      change foldValue f parameter bottomLayer
                        (treeIndexAt (digestIndex digest) bottomLayer)
                        (leafIndexAt (digestIndex digest) bottomLayer)
                        (signaturePath forgery.signature bottomLayer) bottomLeaf
                          (layerHeight bottomLayer) = bottomRoot at hbottomFoldEval
                      subst bottomRoot
                      have hbottomFoldCoordinate :=
                        preservesCoordinate_simulateQ_verifierHashImpl_treeFold_of_layer_ne
                          parameter probe topLayer (treeIndexAt (digestIndex digest) topLayer)
                          (leafIndexAt (digestIndex digest) topLayer) chainIdx
                          ⟨(codeword chainIdx).val, hdigit⟩
                          (forgery.signature.chainValue topLayer chainIdx) hmatches bottomLayer
                          (treeIndexAt (digestIndex digest) bottomLayer)
                          (leafIndexAt (digestIndex digest) bottomLayer)
                          (signaturePath forgery.signature bottomLayer) (by decide)
                          (layerHeight bottomLayer) bottomLeaf (layerHeight_le bottomLayer)
                          bottomOtsState bottomOtsCache bottomOtsRemaining bottomFoldState
                            bottomFoldRemaining
                            (foldValue f parameter bottomLayer
                              (treeIndexAt (digestIndex digest) bottomLayer)
                              (leafIndexAt (digestIndex digest) bottomLayer)
                              (signaturePath forgery.signature bottomLayer) bottomLeaf
                                (layerHeight bottomLayer))
                            bottomFoldCache hbottomFoldRaw
                      simp only at hafterBottomFold
                      rw [show bottomLayer.val = middleLayer.val + 1 by rfl,
                        verifyLayers_succ_eq, dif_pos middleLayer.isLt, simulateQ_bind,
                        StateT.run_bind, LazyRevealProbe.runRaw_bind,
                        mem_support_bind_iff] at hafterBottomFold
                      obtain ⟨middleOtsRaw, hmiddleOtsRaw, hafterMiddleOts⟩ :=
                        hafterBottomFold
                      cases middleOtsRaw with
                      | stopped hit => simp at hafterMiddleOts
                      | done middleOtsState middleOtsRemaining middleOtsResult =>
                          rcases middleOtsResult with ⟨middleResult, middleOtsCache⟩
                          have hfMiddleOts :
                              CacheAnswersAgreeOnRun (ordinaryQueryCache middleOtsCache) f
                                (otsLeaf parameter middleLayer
                                  (treeIndexAt (digestIndex digest) middleLayer)
                                  (leafIndexAt (digestIndex digest) middleLayer)
                                  (foldValue f parameter bottomLayer
                                    (treeIndexAt (digestIndex digest) bottomLayer)
                                    (leafIndexAt (digestIndex digest) bottomLayer)
                                    (signaturePath forgery.signature bottomLayer) bottomLeaf
                                      (layerHeight bottomLayer))
                                  (forgery.signature.counter middleLayer)
                                  (forgery.signature.chainValue middleLayer)) := by
                            intro query hquery output hcached
                            apply hf query
                              (middleOts_query_mem_verify hdigest hadmissible hbottomLeaf hquery)
                            have hcachedLayers :=
                              (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                                middleOtsState middleOtsCache middleOtsRemaining layersState
                                  layersRemaining verifiedRoot layersCache output hcached
                                    hafterMiddleOts
                            exact
                              (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                                layersState layersCache layersRemaining rawState remaining verified
                                  rawCache output hcachedLayers hafterLayers
                          have hmiddleEval :=
                            (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f
                              parameter
                            (otsLeaf parameter middleLayer
                              (treeIndexAt (digestIndex digest) middleLayer)
                              (leafIndexAt (digestIndex digest) middleLayer)
                              (foldValue f parameter bottomLayer
                                (treeIndexAt (digestIndex digest) bottomLayer)
                                (leafIndexAt (digestIndex digest) bottomLayer)
                                (signaturePath forgery.signature bottomLayer) bottomLeaf
                                  (layerHeight bottomLayer))
                              (forgery.signature.counter middleLayer)
                              (forgery.signature.chainValue middleLayer))
                            bottomFoldState middleOtsState bottomFoldCache middleOtsCache
                              bottomFoldRemaining middleOtsRemaining middleResult hfMiddleOts
                                hmiddleOtsRaw).1
                          rw [hmiddleLeaf] at hmiddleEval
                          subst middleResult
                          have hmiddleOtsCoordinate :=
                            preservesCoordinate_simulateQ_verifierHashImpl_otsLeaf_of_layer_ne
                              parameter probe topLayer
                              (treeIndexAt (digestIndex digest) topLayer)
                              (leafIndexAt (digestIndex digest) topLayer) chainIdx
                              ⟨(codeword chainIdx).val, hdigit⟩
                              (forgery.signature.chainValue topLayer chainIdx) hmatches middleLayer
                              (treeIndexAt (digestIndex digest) middleLayer)
                              (leafIndexAt (digestIndex digest) middleLayer)
                              (foldValue f parameter bottomLayer
                                (treeIndexAt (digestIndex digest) bottomLayer)
                                (leafIndexAt (digestIndex digest) bottomLayer)
                                (signaturePath forgery.signature bottomLayer) bottomLeaf
                                  (layerHeight bottomLayer))
                              (forgery.signature.counter middleLayer)
                              (forgery.signature.chainValue middleLayer) (by decide)
                              bottomFoldState bottomFoldCache bottomFoldRemaining middleOtsState
                                middleOtsRemaining (some middleLeaf) middleOtsCache hmiddleOtsRaw
                          simp only at hafterMiddleOts
                          rw [simulateQ_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
                            mem_support_bind_iff] at hafterMiddleOts
                          obtain ⟨middleFoldRaw, hmiddleFoldRaw, hafterMiddleFold⟩ :=
                            hafterMiddleOts
                          cases middleFoldRaw with
                          | stopped hit => simp at hafterMiddleFold
                          | done middleFoldState middleFoldRemaining middleFoldResult =>
                              rcases middleFoldResult with ⟨middleRoot, middleFoldCache⟩
                              have hfMiddleFold :
                                  CacheAnswersAgreeOnRun (ordinaryQueryCache middleFoldCache) f
                                    (treeFold parameter middleLayer
                                      (treeIndexAt (digestIndex digest) middleLayer)
                                      (leafIndexAt (digestIndex digest) middleLayer)
                                      (signaturePath forgery.signature middleLayer)
                                      (layerHeight middleLayer) middleLeaf) := by
                                intro query hquery output hcached
                                apply hf query
                                  (middleFold_query_mem_verify hdigest hadmissible hbottomLeaf
                                    hmiddleLeaf hquery)
                                have hcachedLayers :=
                                  (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                                    middleFoldState middleFoldCache middleFoldRemaining layersState
                                      layersRemaining verifiedRoot layersCache output hcached
                                        hafterMiddleFold
                                exact
                                  (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                                    layersState layersCache layersRemaining rawState remaining
                                      verified rawCache output hcachedLayers hafterLayers
                              have hmiddleFoldEval :=
                                (replay_of_mem_runRaw_verifierHashImpl_of_cacheAnswersAgreeOnRun f
                                  parameter
                                  (treeFold parameter middleLayer
                                    (treeIndexAt (digestIndex digest) middleLayer)
                                    (leafIndexAt (digestIndex digest) middleLayer)
                                    (signaturePath forgery.signature middleLayer)
                                    (layerHeight middleLayer) middleLeaf)
                                  middleOtsState middleFoldState middleOtsCache middleFoldCache
                                    middleOtsRemaining middleFoldRemaining middleRoot hfMiddleFold
                                      hmiddleFoldRaw).1
                              change foldValue f parameter middleLayer
                                (treeIndexAt (digestIndex digest) middleLayer)
                                (leafIndexAt (digestIndex digest) middleLayer)
                                (signaturePath forgery.signature middleLayer) middleLeaf
                                  (layerHeight middleLayer) = middleRoot at hmiddleFoldEval
                              rw [← hlayerMessage] at hmiddleFoldEval
                              subst middleRoot
                              have hmiddleFoldCoordinate :=
                                preservesCoordinate_simulateQ_verifierHashImpl_treeFold_of_layer_ne
                                  parameter probe topLayer
                                  (treeIndexAt (digestIndex digest) topLayer)
                                  (leafIndexAt (digestIndex digest) topLayer) chainIdx
                                  ⟨(codeword chainIdx).val, hdigit⟩
                                  (forgery.signature.chainValue topLayer chainIdx) hmatches
                                  middleLayer (treeIndexAt (digestIndex digest) middleLayer)
                                  (leafIndexAt (digestIndex digest) middleLayer)
                                  (signaturePath forgery.signature middleLayer) (by decide)
                                  (layerHeight middleLayer) middleLeaf (layerHeight_le middleLayer)
                                  middleOtsState middleOtsCache middleOtsRemaining middleFoldState
                                    middleFoldRemaining layerMessage middleFoldCache hmiddleFoldRaw
                              simp only at hafterMiddleFold
                              rw [show middleLayer.val = topLayer.val + 1 by rfl,
                                verifyLayers_succ_eq, dif_pos topLayer.isLt, simulateQ_bind,
                                StateT.run_bind, LazyRevealProbe.runRaw_bind,
                                mem_support_bind_iff] at hafterMiddleFold
                              obtain ⟨topOtsRaw, htopOtsRaw, hafterTopOts⟩ :=
                                hafterMiddleFold
                              cases topOtsRaw with
                              | stopped hit => simp at hafterTopOts
                              | done topOtsState topOtsRemaining topOtsResult =>
                                  rcases topOtsResult with ⟨topResult, topOtsCache⟩
                                  have hfTopOts :
                                      CacheAnswersAgreeOnRun (ordinaryQueryCache topOtsCache) f
                                        (encode parameter topLayer
                                          (treeIndexAt (digestIndex digest) topLayer)
                                          (leafIndexAt (digestIndex digest) topLayer) layerMessage
                                          (forgery.signature.counter topLayer)) := by
                                    intro query hquery output hcached
                                    apply hf query
                                      (VerifierLayerMessage.otsLeaf_query_mem_verify hdigest
                                        hadmissible hverifierMessage (by
                                          unfold otsLeaf
                                          rw [queriedInputs_bind]
                                          exact List.mem_append_left _ hquery))
                                    have hcachedLayers :=
                                      (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                                        topOtsState topOtsCache topOtsRemaining layersState
                                          layersRemaining verifiedRoot layersCache output hcached
                                            hafterTopOts
                                    exact
                                      (ordinaryEntryPreservingImpl_verifierHashImpl parameter query).simulateQ _
                                        layersState layersCache layersRemaining rawState remaining
                                          verified rawCache output hcachedLayers hafterLayers
                                  have hvaluesTopLayers :=
                                    LazyRevealProbe.valuesLE_of_mem_runRaw_done _ topOtsState
                                      layersState topOtsRemaining layersRemaining
                                        (verifiedRoot, layersCache) hafterTopOts
                                  have hvaluesLayersRaw :=
                                    LazyRevealProbe.valuesLE_of_mem_runRaw_done _ layersState
                                      rawState layersRemaining remaining (verified, rawCache)
                                        hafterLayers
                                  have htableTop : ∀ coordinate output,
                                      topOtsState.values coordinate = some output →
                                        output = table coordinate := by
                                    intro coordinate output hvalue
                                    exact hrawTable coordinate output
                                      (hvaluesLayersRaw coordinate output
                                        (hvaluesTopLayers coordinate output hvalue))
                                  have hftsInitial : ftsState = initialState :=
                                    hftsState.1.trans hdigestState.1
                                  have htopInitialValue :
                                      middleFoldState.values probe.coordinate = none := by
                                    rw [hmiddleFoldCoordinate.1, hmiddleOtsCoordinate.1,
                                      hbottomFoldCoordinate.1, hbottomOtsCoordinate.1,
                                      hftsInitial, hinitialValue]
                                  have htopInitialNotRevealed :
                                      probe.coordinate ∉ middleFoldState.revealed := by
                                    rw [hmiddleFoldCoordinate.2, hmiddleOtsCoordinate.2,
                                      hbottomFoldCoordinate.2, hbottomOtsCoordinate.2, hftsInitial]
                                    exact hinitialNotRevealed
                                  have hpendingTop :=
                                    simulateQ_verifierHashImpl_otsLeaf_pendingHit_of_correct_probe
                                      f parameter table probe topLayer
                                      (treeIndexAt (digestIndex digest) topLayer)
                                      (leafIndexAt (digestIndex digest) topLayer) layerMessage
                                      (forgery.signature.counter topLayer)
                                      (forgery.signature.chainValue topLayer) codeword chainIdx
                                      hdigit hencode middleFoldState topOtsState middleFoldCache
                                      topOtsCache middleFoldRemaining topOtsRemaining topResult
                                      hmatches hcandidate htopInitialValue htopInitialNotRevealed
                                      hfTopOts htableTop htopOtsRaw
                                  have htableLayers : ∀ output,
                                      layersState.values probe.coordinate = some output →
                                        output = table probe.coordinate := by
                                    intro output hvalue
                                    exact hrawTable probe.coordinate output
                                      (hvaluesLayersRaw probe.coordinate output hvalue)
                                  have hpendingLayers :=
                                    LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done _
                                      probe.coordinate (table probe.coordinate) topOtsState
                                      layersState topOtsRemaining layersRemaining
                                      (verifiedRoot, layersCache) hpendingTop.1 hpendingTop.2
                                      htableLayers hafterTopOts
                                  have hpendingRaw :=
                                    LazyRevealProbe.pendingHit_preserved_of_mem_runRaw_done _
                                      probe.coordinate (table probe.coordinate) layersState rawState
                                      layersRemaining remaining (verified, rawCache)
                                      hpendingLayers.1 hpendingLayers.2
                                      (hrawTable probe.coordinate) hafterLayers
                                  exact finalizeDetailed_false_of_pending_hit table rawState
                                    completedState probe.coordinate hpendingRaw.1 hpendingRaw.2
                                      (hcompletedTable probe.coordinate) hfinalize

set_option maxRecDepth 10000 in
theorem ChainInvariant.not_finalized_false_of_verifyProbe_verifier
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {table : Coordinate → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {targetCache : QueryCache HashSpec}
    {initialState rawState completedState : LazyRevealProbe.State Coordinate}
    {initialCache rawCache : SplitHashCache} {root : Digest} {forgery : Forgery}
    {signingLog : QueryLog SigningSpec} {fuel remaining : Nat} {verified : Bool}
    (hinvariant : ChainInvariant parameter
      (CoveredChainCoordinate f targetCache
        (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey) signingLog)
      initialState initialCache)
    (hf : CacheAnswersAgreeOnRun (ordinaryQueryCache rawCache) f
      (verify ⟨root, parameter⟩ forgery.message forgery.signature))
    (hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hverify : LazyRevealProbe.RawResult.done rawState remaining
        (verified, rawCache) ∈ support
      (LazyRevealProbe.runRaw initialState fuel
        ((simulateQ (verifierRomImpl parameter)
          (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)).run
            initialCache)))
    (hprobe : VerifyProbeWitness f targetCache
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  rcases hprobe.at_bottom_or_middle_or_top with hbottom | hmiddle | htop
  · exact hinvariant.not_finalized_false_of_bottom_verifyProbe_verifier hf hcompletedTable
      hrealizes hfinalize hverify hbottom
  · exact hinvariant.not_finalized_false_of_middle_verifyProbe_verifier hf hcompletedTable
      hrealizes hfinalize hverify hmiddle
  · exact hinvariant.not_finalized_false_of_top_verifyProbe_verifier hf hcompletedTable
      hrealizes hfinalize hverify htop

set_option maxRecDepth 10000 in
theorem not_verifyProbe_of_mem_runRaw_maskedRetainedGameAfterFtsSecrets
    (adversary : Adversary) (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (table : Coordinate → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel remaining : Nat) (rawState completedState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hfStable : StableCacheAgreesWithFn parameter rawCache f)
    (hfOrdinary : CacheAnswersAgreeOnRun (ordinaryQueryCache rawCache) f
      (verify ⟨root, parameter⟩ forgery.message forgery.signature))
    (hrawTable : ∀ coordinate output, rawState.values coordinate = some output →
      output = table coordinate)
    (hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate)
    (hrealizes : ∀ position : Position, IsOtsPosition position →
      f (tableInput parameter table (.position position)) = table (.position position))
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hprobe : VerifyProbeWitness f
      (mergedCache parameter table rawState.ensured rawCache)
      (⟨parameter, root, tableOtsSecret table, ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  obtain ⟨verifierState, verifierFuel, verifierCache, hinvariant, hverify⟩ :=
    chainInvariant_maskedRetainedGameAfterFtsSecrets_mergedCache adversary f parameter table
      ftsSecret fuel remaining rawState rawCache root forgery signingLog verified hfStable
        hrawTable hrealizes hresult
  exact hinvariant.not_finalized_false_of_verifyProbe_verifier hfOrdinary hcompletedTable
    hrealizes hfinalize hverify hprobe

theorem finalizeDetailedFrom_ensured_eq :
    ∀ (coordinates : List Coordinate) (state finalState : LazyRevealProbe.State Coordinate),
      (false, finalState) ∈ support
        (LazyRevealProbe.finalizeDetailedFrom coordinates state) →
      finalState.ensured = state.ensured := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state finalState hresult
      simp [LazyRevealProbe.finalizeDetailedFrom] at hresult
      exact congrArg LazyRevealProbe.State.ensured hresult
  | cons coordinate coordinates ih =>
      intro state finalState hresult
      rw [LazyRevealProbe.finalizeDetailedFrom] at hresult
      cases hvalue : state.values coordinate with
      | some output =>
          rw [hvalue] at hresult
          exact (ih (state.clearPending coordinate) finalState hresult).trans (by
            simp [LazyRevealProbe.State.clearPending])
      | none =>
          rw [hvalue, mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          by_cases hhit : state.hitAt coordinate output
          · rw [if_pos hhit] at hrest
            simp at hrest
          · rw [if_neg hhit] at hrest
            exact (ih (state.complete coordinate output) finalState hrest).trans (by
              simp [LazyRevealProbe.State.complete])

theorem finalizeDetailed_ensured_eq
    (state finalState : LazyRevealProbe.State Coordinate)
    (hresult : (false, finalState) ∈ support
      (LazyRevealProbe.finalizeDetailed state)) :
    finalState.ensured = state.ensured :=
  finalizeDetailedFrom_ensured_eq state.coordinates.toList state finalState hresult

theorem retainedCompletion_of_finalize
    (parameter : PublicParameter)
    (rawState completedState : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (hconsistent : HiddenConsistent rawState cache)
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState)) :
    let table := retainedCompletionTable parameter completedState cache baseStarts
    let f := retainedCompletionAnswer parameter completedState cache baseStarts
    StableCacheAgreesWithFn parameter cache f ∧
      (mergedCache parameter table rawState.ensured cache).AgreesWithFn f ∧
      (∀ coordinate output, rawState.values coordinate = some output →
        output = table coordinate) ∧
      (∀ coordinate output, completedState.values coordinate = some output →
        output = table coordinate) ∧
      (∀ position : Position, IsOtsPosition position →
        f (tableInput parameter table (.position position)) = table (.position position)) := by
  let table := retainedCompletionTable parameter completedState cache baseStarts
  let f := retainedCompletionAnswer parameter completedState cache baseStarts
  have hensured := finalizeDetailed_ensured_eq rawState completedState hfinalize
  have hcompletedConsistent :=
    finalizeDetailed_preservesHidden rawState cache hconsistent completedState hfinalize
  have hcompletedTable : ∀ coordinate output,
      completedState.values coordinate = some output → output = table coordinate := by
    intro coordinate output hvalue
    exact (completedRealizedTable_of_value (splitFallback cache) parameter completedState
      baseStarts coordinate output hvalue).symm
  have hrawTable : ∀ coordinate output,
      rawState.values coordinate = some output → output = table coordinate := by
    intro coordinate output hvalue
    exact hcompletedTable coordinate output
      (finalizeDetailedFrom_preserves_value rawState.coordinates.toList rawState completedState
        coordinate output hvalue hfinalize)
  refine ⟨stableCacheAgreesWithFn_retainedCompletionAnswer parameter completedState cache
      baseStarts, ?_, hrawTable, hcompletedTable,
      retainedCompletionAnswer_realizes parameter completedState cache baseStarts⟩
  rw [← hensured]
  exact mergedCache_agreesWithFn_retainedCompletionAnswer parameter completedState cache
    baseStarts hcompletedConsistent

set_option maxRecDepth 10000 in
theorem not_verifyProbe_of_retainedCompletion
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (fuel remaining : Nat) (rawState completedState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hconsistent : HiddenConsistent rawState rawCache)
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hfOrdinary : CacheAnswersAgreeOnRun (ordinaryQueryCache rawCache)
      (retainedCompletionAnswer parameter completedState rawCache baseStarts)
      (verify ⟨root, parameter⟩ forgery.message forgery.signature))
    (hprobe : VerifyProbeWitness
      (retainedCompletionAnswer parameter completedState rawCache baseStarts)
      (mergedCache parameter
        (retainedCompletionTable parameter completedState rawCache baseStarts)
        completedState.ensured rawCache)
      (⟨parameter, root,
        tableOtsSecret (retainedCompletionTable parameter completedState rawCache baseStarts),
        ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  obtain ⟨hfStable, _hfMerged, hrawTable, hcompletedTable, hrealizes⟩ :=
    retainedCompletion_of_finalize parameter rawState completedState rawCache baseStarts
      hconsistent hfinalize
  have hensured := finalizeDetailed_ensured_eq rawState completedState hfinalize
  rw [hensured] at hprobe
  exact not_verifyProbe_of_mem_runRaw_maskedRetainedGameAfterFtsSecrets adversary
    (retainedCompletionAnswer parameter completedState rawCache baseStarts) parameter
    (retainedCompletionTable parameter completedState rawCache baseStarts) ftsSecret fuel
    remaining rawState completedState rawCache root forgery signingLog verified hfStable
    hfOrdinary hrawTable hcompletedTable hrealizes hresult hfinalize hprobe

set_option maxRecDepth 10000 in
theorem not_verifyProbe_of_retainedCompletion_of_trace_exact_materialized
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (fuel remaining : Nat) (rawState completedState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hconsistent : HiddenConsistent rawState rawCache)
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hexact : TraceExactMaterializedCacheConsistent parameter
      (retainedCompletionTable parameter completedState rawCache baseStarts)
      completedState rawCache
      (retainedCompletionAnswer parameter completedState rawCache baseStarts)
      (verify ⟨root, parameter⟩ forgery.message forgery.signature))
    (hprobe : VerifyProbeWitness
      (retainedCompletionAnswer parameter completedState rawCache baseStarts)
      (mergedCache parameter
        (retainedCompletionTable parameter completedState rawCache baseStarts)
        completedState.ensured rawCache)
      (⟨parameter, root,
        tableOtsSecret (retainedCompletionTable parameter completedState rawCache baseStarts),
        ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  apply not_verifyProbe_of_retainedCompletion adversary parameter ftsSecret baseStarts fuel
    remaining rawState completedState rawCache root forgery signingLog verified hconsistent
    hresult hfinalize
  · exact cacheAnswersAgreeOnRun_retainedCompletionAnswer_of_trace_exact_materialized
      parameter completedState rawCache baseStarts
        (verify ⟨root, parameter⟩ forgery.message forgery.signature) hexact
  · exact hprobe

set_option maxRecDepth 10000 in
theorem not_verifyProbe_of_retainedCompletion_of_exact_materialized
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (fuel remaining : Nat) (rawState completedState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hconsistent : HiddenConsistent rawState rawCache)
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hexact : ∀ (input : HashInput) (position : Position) (output : HashOutput),
      IsOtsPosition position →
      decodePosition? parameter input = some position →
      input = tableInput parameter
        (retainedCompletionTable parameter completedState rawCache baseStarts)
          (.position position) →
      completedState.values (.position position) ≠ none →
      rawCache (.ordinary input) = some output →
      output = retainedCompletionTable parameter completedState rawCache baseStarts
        (.position position))
    (hprobe : VerifyProbeWitness
      (retainedCompletionAnswer parameter completedState rawCache baseStarts)
      (mergedCache parameter
        (retainedCompletionTable parameter completedState rawCache baseStarts)
        completedState.ensured rawCache)
      (⟨parameter, root,
        tableOtsSecret (retainedCompletionTable parameter completedState rawCache baseStarts),
        ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  apply not_verifyProbe_of_retainedCompletion_of_trace_exact_materialized adversary parameter
    ftsSecret baseStarts fuel
    remaining rawState completedState rawCache root forgery signingLog verified hconsistent
    hresult hfinalize
  · intro input _ position output hots hposition hinput hvalue hcached
    exact hexact input position output hots hposition hinput hvalue hcached
  · exact hprobe

set_option maxRecDepth 10000 in
theorem not_verifyProbe_of_retainedCompletion_of_clean_finalize
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (baseStarts : Layer → TreeIndex → LeafIndex → ChainIndex → HashOutput)
    (fuel remaining : Nat) (rawState completedState : LazyRevealProbe.State Coordinate)
    (rawCache : SplitHashCache) (root : Digest) (forgery : Forgery)
    (signingLog : QueryLog SigningSpec) (verified : Bool)
    (hconsistent : HiddenConsistent rawState rawCache)
    (hresult : LazyRevealProbe.RawResult.done rawState remaining
        ((root, ((forgery, signingLog), verified)), rawCache) ∈ support
      (LazyRevealProbe.runRaw (LazyRevealProbe.State.empty :
          LazyRevealProbe.State Coordinate) fuel
        ((maskedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
          emptySplitHashCache)))
    (hfinalize : (false, completedState) ∈ support
      (LazyRevealProbe.finalizeDetailed rawState))
    (hprobe : VerifyProbeWitness
      (retainedCompletionAnswer parameter completedState rawCache baseStarts)
      (mergedCache parameter
        (retainedCompletionTable parameter completedState rawCache baseStarts)
        completedState.ensured rawCache)
      (⟨parameter, root,
        tableOtsSecret (retainedCompletionTable parameter completedState rawCache baseStarts),
        ftsSecret⟩ : SecretKey)
      signingLog forgery.message forgery.signature) : False := by
  obtain ⟨_, _, _, hcompletedTable, _⟩ :=
    retainedCompletion_of_finalize parameter rawState completedState rawCache baseStarts
      hconsistent hfinalize
  apply not_verifyProbe_of_retainedCompletion_of_exact_materialized adversary parameter
    ftsSecret baseStarts fuel remaining rawState completedState rawCache root forgery signingLog
      verified hconsistent hresult hfinalize
  · exact exactMaterializedCacheConsistent_of_clean_finalize adversary parameter
      (retainedCompletionTable parameter completedState rawCache baseStarts) ftsSecret fuel
        remaining rawState completedState rawCache root forgery signingLog verified
          hcompletedTable hresult hfinalize
  · exact hprobe

theorem relTriple_runRaw_splitUniformImpl
    (n : Nat) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
        pure (output, ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := Fin (n + 1)) state fuel) := by
  let uniform : ProbComp (Fin (n + 1)) := liftM (unifSpec.query n)
  have hself : RelTriple uniform uniform fun left right => left = right :=
    relTriple_refl uniform
  have hpre : RelTriple uniform uniform fun left right =>
      RawOrdinaryResultRelAt state fuel
        (.done state fuel (left, cache)) (right, ordinaryQueryCache cache) := by
    apply relTriple_post_mono hself
    intro left right heq
    subst right
    simp [RawOrdinaryResultRelAt]
  have hmapped := relTriple_map
    (R := RawOrdinaryResultRelAt (alpha := Fin (n + 1)) state fuel)
    (f := fun output => LazyRevealProbe.RawResult.done state fuel (output, cache))
    (g := fun output => (output, ordinaryQueryCache cache)) hpre
  simpa [uniform, splitUniformImpl, LazyRevealProbe.uniformQuery,
    LazyRevealProbe.runRaw_uniform_query_bind, LazyRevealProbe.runRaw,
    map_eq_bind_pure_comp] using hmapped

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryHashImpl
    [Inhabited alpha]
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (RawOrdinaryResultRel (alpha := alpha)) := by
  have hproject :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_of_project_eq_some_exact
      projectRawOrdinary
      (default, ∅)
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (projectRawOrdinary_simulateQ_ordinaryHashImpl computation state cache fuel)
  apply relTriple_post_mono hproject
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => simp [projectRawOrdinary] at hrelation
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      change ordinaryResult = (value, ordinaryQueryCache finalCache)
      exact (Option.some.inj hrelation).symm

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryHashImpl_at
    [Inhabited alpha]
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := alpha) state fuel) := by
  have hbase := relTriple_runRaw_simulateQ_ordinaryHashImpl computation state cache fuel
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => match result with
        | .stopped _ => True
        | .done finalState remaining _ => finalState = state ∧ remaining = fuel)
      (by
        intro result hresult
        cases result with
        | stopped hit => trivial
        | done finalState remaining valueCache =>
            rcases valueCache with ⟨value, finalCache⟩
            have hprojection := mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state
              finalState cache finalCache fuel remaining value hresult
            exact ⟨hprojection.1, hprojection.2.1⟩)
  apply relTriple_post_mono hsupported
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => exact hrelation.1
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      exact ⟨hrelation.2.1, hrelation.2.2, hrelation.1⟩

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryRomImpl
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryRomImpl computation).run cache))
      ((simulateQ romImpl computation).run (ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := alpha) state fuel) := by
  induction computation using OracleComp.inductionOn generalizing state cache fuel with
  | pure value =>
      simp [LazyRevealProbe.runRaw, RawOrdinaryResultRelAt]
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        simulateQ_query_bind, StateT.run_bind]
      have hquery : RelTriple
          (LazyRevealProbe.runRaw state fuel ((ordinaryRomImpl query).run cache))
          ((romImpl query).run (ordinaryQueryCache cache))
          (RawOrdinaryResultRelAt state fuel) := by
        cases query with
        | inl n =>
            change RelTriple
              (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))
              ((unifFwdImpl HashSpec n).run (ordinaryQueryCache cache))
              (RawOrdinaryResultRelAt state fuel)
            rw [show (unifFwdImpl HashSpec n).run (ordinaryQueryCache cache) =
                (fun output => (output, ordinaryQueryCache cache)) <$>
                  (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) by
              simpa using unifFwdImpl.simulateQ_run
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
                (ordinaryQueryCache cache)]
            simpa [map_eq_bind_pure_comp] using
              relTriple_runRaw_splitUniformImpl n state cache fuel
        | inr input =>
            simpa [ordinaryRomImpl, romImpl] using
              relTriple_runRaw_simulateQ_ordinaryHashImpl_at
                (liftM (HashSpec.query input)) state cache fuel
      apply relTriple_bind hquery
      intro rawResult ordinaryResult hrelation
      cases rawResult with
      | stopped hit => simp [RawOrdinaryResultRelAt] at hrelation
      | done finalState remaining valueCache =>
          rcases valueCache with ⟨value, finalCache⟩
          rcases hrelation with ⟨rfl, rfl, rfl⟩
          exact ih value finalState finalCache remaining

set_option maxRecDepth 10000 in
theorem evalDist_projectRawOrdinary_simulateQ_ordinaryRomImpl
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    𝒟[projectRawOrdinary <$>
        LazyRevealProbe.runRaw state fuel
          ((simulateQ ordinaryRomImpl computation).run cache)] =
      𝒟[some <$>
        (simulateQ romImpl computation).run (ordinaryQueryCache cache)] := by
  refine evalDist_map_eq_of_relTriple (relTriple_post_mono
    (relTriple_runRaw_simulateQ_ordinaryRomImpl computation state cache fuel) ?_)
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => simp [RawOrdinaryResultRelAt] at hrelation
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      rcases hrelation with ⟨_, _, rfl⟩
      rfl

set_option maxRecDepth 10000 in
theorem mem_runRaw_simulateQ_ordinaryRomImpl_projects
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryRomImpl computation).run cache))) :
    finalState = state ∧ remaining = fuel ∧
      (value, ordinaryQueryCache finalCache) ∈ support
        ((simulateQ romImpl computation).run (ordinaryQueryCache cache)) := by
  obtain ⟨ordinaryResult, hordinary, hrelation⟩ :=
    exists_right_mem_support_of_relTriple
      (relTriple_runRaw_simulateQ_ordinaryRomImpl computation state cache fuel) hresult
  exact ⟨hrelation.1, hrelation.2.1, hrelation.2.2 ▸ hordinary⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
