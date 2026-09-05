import SphincsSecurity.Proof.OtsProbePublicHashValues
import SphincsSecurity.Proof.OtsProbeStartHistorySupport
import SphincsSecurity.Proof.OtsProbeHistoryAdaptiveInterpreter

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedSignLayer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem resolvedPreservesCoordinate_sequenceFin (coordinate : Coordinate) {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, ResolvedPreservesCoordinate coordinate (computation index)) :
    ResolvedPreservesCoordinate coordinate (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using resolvedPreservesCoordinate_pure coordinate Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ) (fun index => hcomponent index.succ)).bind
          fun _ => resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesCoordinate_simulateQ_ordinaryHashImpl (coordinate : Coordinate)
    (computation : OracleComp HashSpec α) :
    ResolvedPreservesCoordinate coordinate (simulateQ ordinaryHashImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact resolvedPreservesCoordinate_pure coordinate value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      exact (resolvedPreservesCoordinate_splitHashQuery coordinate (.ordinary input)).bind ih

theorem resolvedPreservesCoordinate_revealCoordinate_of_ne
    (coordinate revealed : Coordinate) (hne : coordinate ≠ revealed) :
    ResolvedPreservesCoordinate coordinate (revealCoordinate revealed) := by
  unfold revealCoordinate
  exact (resolvedPreservesCoordinate_revealCoordinateOutput_of_ne coordinate revealed hne).bind fun _ =>
    resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesCoordinate_ensureFullChain
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ResolvedPreservesCoordinate coordinate (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun _ =>
    resolvedPreservesCoordinate_ensure coordinate _).bind fun _ => resolvedPreservesCoordinate_pure coordinate ()

theorem resolvedPreservesCoordinate_ensureOtsLeaf
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesCoordinate coordinate (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun chainIdx =>
    resolvedPreservesCoordinate_ensureFullChain coordinate lay tree leafIdx chainIdx).bind fun _ =>
      resolvedPreservesCoordinate_ensure coordinate _

theorem resolvedPreservesCoordinate_ensureTreeNode
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    ResolvedPreservesCoordinate coordinate (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact resolvedPreservesCoordinate_ensureOtsLeaf coordinate lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (resolvedPreservesCoordinate_ensureTreeNode coordinate lay tree level (2 * nodeIdx)).bind fun _ =>
        (resolvedPreservesCoordinate_ensureTreeNode coordinate lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          split
          · exact resolvedPreservesCoordinate_ensure coordinate _
          · exact resolvedPreservesCoordinate_pure coordinate ()

theorem resolvedPreservesStart_maskedTreeNode
    (start : OtsSecretIndex) (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    ResolvedPreservesCoordinate start.coordinate (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (resolvedPreservesCoordinate_ensureTreeNode start.coordinate lay tree 0 nodeIdx).bind fun _ =>
        resolvedPreservesCoordinate_revealCoordinate_of_ne start.coordinate _ (by simp [OtsSecretIndex.coordinate])
  | succ current =>
      rw [maskedTreeNode]
      exact (resolvedPreservesCoordinate_ensureTreeNode start.coordinate lay tree (current + 1) nodeIdx).bind fun _ => by
        split
        · exact resolvedPreservesCoordinate_revealCoordinate_of_ne start.coordinate _ (by simp [OtsSecretIndex.coordinate])
        · exact resolvedPreservesCoordinate_pure start.coordinate 0

theorem resolvedPreservesStart_maskedLayerMessage
    (start : OtsSecretIndex) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ResolvedPreservesCoordinate start.coordinate (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact resolvedPreservesStart_maskedTreeNode start _ _ _ _
  · exact resolvedPreservesCoordinate_simulateQ_ordinaryHashImpl start.coordinate _

theorem resolvedPreservesCoordinate_ensureChainPrefix
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    ResolvedPreservesCoordinate coordinate (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun _ => by
    split
    · exact resolvedPreservesCoordinate_ensure coordinate _
    · exact resolvedPreservesCoordinate_pure coordinate ()).bind fun _ => resolvedPreservesCoordinate_pure coordinate ()

theorem resolvedPreservesCoordinate_maskedOtsSignFrom
    (coordinate : Coordinate) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    ResolvedPreservesCoordinate coordinate (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => resolvedPreservesCoordinate_pure coordinate none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (resolvedPreservesCoordinate_simulateQ_ordinaryHashImpl coordinate _).bind fun encoded =>
        match encoded with
        | none => resolvedPreservesCoordinate_maskedOtsSignFrom coordinate parameter lay tree leafIdx message
            attempts (counter + 1)
        | some encoding =>
            (resolvedPreservesCoordinate_sequenceFin coordinate _ fun chainIdx =>
              resolvedPreservesCoordinate_ensureChainPrefix coordinate lay tree leafIdx chainIdx (encoding chainIdx)).bind
                fun _ => resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesCoordinate_ensureTreePath
    (coordinate : Coordinate) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesCoordinate coordinate (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (resolvedPreservesCoordinate_sequenceFin coordinate _ fun _ => by
    split
    · exact resolvedPreservesCoordinate_ensureTreeNode coordinate lay tree _ _
    · exact resolvedPreservesCoordinate_pure coordinate ()).bind fun _ => resolvedPreservesCoordinate_pure coordinate ()

theorem resolvedPreservesStart_maskedSignLayer
    (start : OtsSecretIndex) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ResolvedPreservesCoordinate start.coordinate (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (resolvedPreservesStart_maskedLayerMessage start parameter ftsSecret index lay).bind fun message =>
    (resolvedPreservesCoordinate_maskedOtsSignFrom start.coordinate parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) message encodingAttemptLimit 0).bind fun selected =>
        match selected with
        | none => resolvedPreservesCoordinate_pure start.coordinate none
        | some _ =>
            (resolvedPreservesCoordinate_ensureTreePath start.coordinate lay (treeIndexAt index lay)
              (leafIndexAt index lay)).bind fun _ => resolvedPreservesCoordinate_pure start.coordinate _

theorem resolvedPreservesStart_revealPrivateLayerValues
    (start : OtsSecretIndex) (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (hother : ∀ chainIdx, start.coordinate ≠
      chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx)) :
    ResolvedPreservesCoordinate start.coordinate (revealPrivateLayerValues index lay encoding) := by
  unfold revealPrivateLayerValues
  exact (resolvedPreservesCoordinate_sequenceFin start.coordinate _ fun chainIdx =>
    resolvedPreservesCoordinate_revealCoordinate_of_ne start.coordinate _ (hother chainIdx)).bind fun _ =>
      (resolvedPreservesCoordinate_sequenceFin start.coordinate _ fun level => by
        by_cases hinLayer : level.val < layerHeight lay
        · simp only [hinLayer, if_pos]
          cases hlevelValue : level.val with
          | zero =>
              exact resolvedPreservesCoordinate_revealCoordinate_of_ne start.coordinate _ (by simp [OtsSecretIndex.coordinate])
          | succ current =>
              by_cases hcurrent : current < maxLayerHeight
              · simp only [hcurrent, dite_true]
                exact resolvedPreservesCoordinate_revealCoordinate_of_ne start.coordinate _ (by simp [OtsSecretIndex.coordinate])
              · simp only [hcurrent, dite_false]
                exact resolvedPreservesCoordinate_pure start.coordinate 0
        · simp only [hinLayer, if_false]
          exact resolvedPreservesCoordinate_pure start.coordinate 0).bind fun _ =>
          resolvedPreservesCoordinate_pure start.coordinate _

def ResolvedPreservesCoordinateWhen (coordinate : Coordinate)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (condition : α → Prop) : Prop :=
  ∀ context fuel table cache result,
    some result ∈ support (runResolvedFromTable context fuel table (computation.run cache)) →
    condition result.value.1 → result.context.state.values coordinate = context.state.values coordinate

theorem resolvedPreservesCoordinateWhen_sequenceFin (coordinate : Coordinate) {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (condition : Fin n → α → Prop)
    (hcomponent : ∀ index, ResolvedPreservesCoordinateWhen coordinate (computation index) (condition index)) :
    ResolvedPreservesCoordinateWhen coordinate (sequenceFin computation) (fun values => ∀ index, condition index (values index)) := by
  induction n with
  | zero =>
      intro context fuel table cache result hresult _
      simp [sequenceFin, runResolvedFromTable] at hresult
      subst result
      rfl
  | succ n ih =>
      intro context fuel table cache result hresult hcondition
      rw [sequenceFin, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨headOption, hhead, hrest⟩ := hresult
      cases headOption with
      | none => simp at hrest
      | some head =>
          dsimp only at hrest
          rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨tailOption, htail, hreturn⟩ := hrest
          cases tailOption with
          | none => simp at hreturn
          | some tail =>
              simp [runResolvedFromTable] at hreturn
              subst result
              have hheadPreserved := hcomponent 0 context fuel table cache head hhead (hcondition 0)
              have htailPreserved := ih (fun index : Fin n => computation index.succ)
                (fun index value => condition index.succ value) (fun index => hcomponent index.succ)
                head.context head.remaining head.table head.value.2 tail htail (fun index => hcondition index.succ)
              exact htailPreserved.trans hheadPreserved

def StartOutsideLayerPart (start : OtsSecretIndex) (index : Index) (lay : Layer) :
    Option ChronologicalLayerPart → Prop
  | none => True
  | some part => ∀ chainIdx, start.coordinate ≠
      chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (part.encoding chainIdx)

theorem resolvedPreservesStart_maskedChronologicalSignLayer
    (start : OtsSecretIndex) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ResolvedPreservesCoordinateWhen start.coordinate (maskedChronologicalSignLayer parameter ftsSecret index lay)
      (StartOutsideLayerPart start index lay) := by
  intro context fuel table cache result hresult houtside
  rw [maskedChronologicalSignLayer, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨selectedOption, hselected, hrest⟩ := hresult
  cases selectedOption with
  | none => simp at hrest
  | some selected =>
      have hbefore := (resolvedPreservesStart_maskedSignLayer start parameter ftsSecret index lay
        context fuel table cache selected hselected).1
      cases hvalue : selected.value.1 with
      | none =>
          simp [hvalue, runResolvedFromTable] at hrest
          subst result
          exact hbefore
      | some chosen =>
          rcases chosen with ⟨counter, encoding⟩
          simp only [hvalue] at hrest
          rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
          obtain ⟨revealedOption, hreveal, hreturn⟩ := hrest
          cases revealedOption with
          | none => simp at hreturn
          | some revealed =>
              simp [runResolvedFromTable] at hreturn
              subst result
              have hafter := resolvedPreservesStart_revealPrivateLayerValues start index lay encoding houtside
                selected.context selected.remaining selected.table selected.value.2 revealed hreveal
              exact hafter.1.trans hbefore

theorem resolvedPreservesStart_maskedChronologicalSignLayers
    (start : OtsSecretIndex) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ResolvedPreservesCoordinateWhen start.coordinate (maskedChronologicalSignLayers parameter ftsSecret index)
      (fun layers => ∀ lay, StartOutsideLayerPart start index lay (layers lay)) :=
  resolvedPreservesCoordinateWhen_sequenceFin start.coordinate _ _ fun lay =>
    resolvedPreservesStart_maskedChronologicalSignLayer start parameter ftsSecret index lay

def ResolvedPublishes (coordinate : Coordinate)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel table cache result,
    some result ∈ support (runResolvedFromTable context fuel table (computation.run cache)) →
      coordinate ∈ result.context.state.revealed

theorem ResolvedPublishes.bind_left
    {coordinate : Coordinate}
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (hleft : ResolvedPublishes coordinate left) : ResolvedPublishes coordinate (left >>= next) := by
  intro context fuel table cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨option, hleftSupport, hrest⟩ := hresult
  cases option with
  | none => simp at hrest
  | some middle =>
      exact (revealed_subset_of_mem_runResolvedFromTable _ middle.context middle.remaining middle.table result hrest)
        (hleft context fuel table cache middle hleftSupport)

theorem ResolvedPublishes.bind_right
    {coordinate : Coordinate}
    (left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hnext : ∀ value, ResolvedPublishes coordinate (next value)) : ResolvedPublishes coordinate (left >>= next) := by
  intro context fuel table cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨option, _hleft, hrest⟩ := hresult
  cases option with
  | none => simp at hrest
  | some middle =>
      exact hnext middle.value.1 middle.context middle.remaining middle.table middle.value.2 result hrest

theorem resolvedPublishes_publishCoordinate (coordinate : Coordinate) :
    ResolvedPublishes coordinate (publishCoordinate coordinate) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.publishQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, runResolvedFromTable_publish_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  simp [LazyRevealProbe.State.publish]

theorem resolvedPublishes_revealPublishedCoordinate (coordinate : Coordinate) :
    ResolvedPublishes coordinate (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact ResolvedPublishes.bind_right _ fun _ => (resolvedPublishes_publishCoordinate coordinate).bind_left _

theorem resolvedPublishes_sequenceFin (coordinate : Coordinate) {n : Nat}
    (computation : Fin n → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (index : Fin n) (hcomponent : ResolvedPublishes coordinate (computation index)) :
    ResolvedPublishes coordinate (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      rw [sequenceFin]
      cases index using Fin.cases with
      | zero => exact hcomponent.bind_left _
      | succ index =>
          exact ResolvedPublishes.bind_right _ fun _ =>
            (ih (fun index : Fin n => computation index.succ) index hcomponent).bind_left _

theorem resolvedPublishes_revealLayerValues (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) (chainIdx : ChainIndex) :
    ResolvedPublishes
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx))
      (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (resolvedPublishes_sequenceFin _ _ chainIdx (resolvedPublishes_revealPublishedCoordinate _)).bind_left _

theorem resolvedPreservesCoordinate_revealPublishedCoordinate_of_ne
    (coordinate published : Coordinate) (hne : coordinate ≠ published) :
    ResolvedPreservesCoordinate coordinate (revealPublishedCoordinate published) := by
  unfold revealPublishedCoordinate
  exact (resolvedPreservesCoordinate_revealCoordinate_of_ne coordinate published hne).bind fun _ =>
    (resolvedPreservesCoordinate_publish_of_ne coordinate published hne).bind fun _ =>
      resolvedPreservesCoordinate_pure coordinate _

theorem resolvedPreservesStart_revealLayerValues
    (start : OtsSecretIndex) (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (hother : ∀ chainIdx, start.coordinate ≠
      chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx)) :
    ResolvedPreservesCoordinate start.coordinate (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (resolvedPreservesCoordinate_sequenceFin start.coordinate _ fun chainIdx =>
    resolvedPreservesCoordinate_revealPublishedCoordinate_of_ne start.coordinate _ (hother chainIdx)).bind fun _ =>
      (resolvedPreservesCoordinate_sequenceFin start.coordinate _ fun level => by
        by_cases hinLayer : level.val < layerHeight lay
        · simp only [hinLayer, if_pos]
          cases hlevelValue : level.val with
          | zero =>
              exact resolvedPreservesCoordinate_revealPublishedCoordinate_of_ne start.coordinate _ (by simp [OtsSecretIndex.coordinate])
          | succ current =>
              by_cases hcurrent : current < maxLayerHeight
              · simp only [hcurrent, dite_true]
                exact resolvedPreservesCoordinate_revealPublishedCoordinate_of_ne start.coordinate _ (by simp [OtsSecretIndex.coordinate])
              · simp only [hcurrent, dite_false]
                exact resolvedPreservesCoordinate_pure start.coordinate 0
        · simp only [hinLayer, if_false]
          exact resolvedPreservesCoordinate_pure start.coordinate 0).bind fun _ =>
          resolvedPreservesCoordinate_pure start.coordinate _

def MaterializedStartsPublished (context : DeferredContext) : Prop :=
  ∀ start : OtsSecretIndex, context.state.values start.coordinate ≠ none → start.coordinate ∈ context.state.revealed

theorem materializedStartsPublished_of_canonical
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hcanonical : CanonicalMaterializedValues table context) : MaterializedStartsPublished context := by
  intro start hvalue
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hvalue
  exact MaterializedValuesPublished.of_canonical hcanonical start.coordinate output houtput

theorem materializedStartsPublished_of_signLayers_and_publish
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (layerResult : ResolvedRunResult ((Layer → Option ChronologicalLayerPart) × SplitHashCache))
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublic : MaterializedStartsPublished context)
    (hlayers : some layerResult ∈ support (runResolvedFromTable context fuel table
      ((maskedChronologicalSignLayers parameter ftsSecret index).run cache)))
    (hresult : some result ∈ support (runResolvedFromTable layerResult.context layerResult.remaining layerResult.table
      ((publishChronologicalSignature ftsSecret randomness index leaves ftsPath layerResult.value.1).run layerResult.value.2)))
    (hsuccess : result.value.1 ≠ none) : MaterializedStartsPublished result.context := by
  classical
  cases hparts : traverseOption layerResult.value.1 with
  | none =>
      simp [publishChronologicalSignature, hparts, runResolvedFromTable] at hresult
      subst result
      exact False.elim (hsuccess rfl)
  | some parts =>
      rw [publishChronologicalSignature, hparts, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
      obtain ⟨publishedOption, hpublished, hreturn⟩ := hresult
      cases publishedOption with
      | none => simp at hreturn
      | some published =>
          simp [runResolvedFromTable] at hreturn
          subst result
          intro start hvalue
          by_cases hselected : ∃ lay chainIdx, start.coordinate =
              chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx)
          · obtain ⟨lay, chainIdx, heq⟩ := hselected
            rw [heq]
            exact resolvedPublishes_sequenceFin _ _ lay
              (resolvedPublishes_revealLayerValues index lay (parts lay).encoding chainIdx)
              layerResult.context layerResult.remaining layerResult.table layerResult.value.2 published hpublished
          · have hother : ∀ lay chainIdx, start.coordinate ≠
                chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx ((parts lay).encoding chainIdx) := by
              intro lay chainIdx heq
              exact hselected ⟨lay, chainIdx, heq⟩
            have hafter := resolvedPreservesCoordinate_sequenceFin start.coordinate _
              (fun lay => resolvedPreservesStart_revealLayerValues start index lay (parts lay).encoding (hother lay))
              layerResult.context layerResult.remaining layerResult.table layerResult.value.2 published hpublished
            have hbefore := resolvedPreservesStart_maskedChronologicalSignLayers start parameter ftsSecret index
              context fuel table cache layerResult hlayers (by
                intro lay
                rw [traverseOption_eq_some_apply layerResult.value.1 parts hparts lay]
                exact hother lay)
            have hinitial : context.state.values start.coordinate ≠ none := by
              rwa [hafter.1, hbefore] at hvalue
            exact hafter.2.mpr ((revealed_subset_of_mem_runResolvedFromTable _ context fuel table layerResult hlayers)
              (hpublic start hinitial))

theorem materializedStartsPublished_of_mem_successful_signAfterDigest
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublic : MaterializedStartsPublished context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves).run cache)))
    (hsuccess : result.value.1 ≠ none) : MaterializedStartsPublished result.context := by
  rw [maskedPublishedChronologicalSignAfterDigest_eq, StateT.run_bind, runResolvedFromTable_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨pathOption, hpath, hrest⟩ := hresult
  cases pathOption with
  | none => simp at hrest
  | some path =>
      have hpathPublic : MaterializedStartsPublished path.context := by
        intro start hvalue
        have hpreserved := resolvedPreservesCoordinate_simulateQ_ordinaryHashImpl start.coordinate _
          context fuel table cache path hpath
        exact hpreserved.2.mpr (hpublic start (by rwa [hpreserved.1] at hvalue))
      dsimp only at hrest
      rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
      obtain ⟨layerOption, hlayers, hpublish⟩ := hrest
      cases layerOption with
      | none => simp at hpublish
      | some layers =>
          exact materializedStartsPublished_of_signLayers_and_publish parameter ftsSecret randomness index leaves
            path.value.1 path.context path.remaining path.table path.value.2 layers result hpathPublic hlayers hpublish hsuccess

theorem resolvedPreservesCoordinate_splitUniformImpl (coordinate : Coordinate) (n : Nat) :
    ResolvedPreservesCoordinate coordinate (splitUniformImpl n) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, hreturn⟩ := hresult
  simp [runResolvedFromTable] at hreturn
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl (coordinate : Coordinate)
    (computation : OracleComp OracleWorld α) :
    ResolvedPreservesCoordinate coordinate (simulateQ ordinaryRomImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact resolvedPreservesCoordinate_pure coordinate value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      apply ResolvedPreservesCoordinate.bind ?_ ih
      cases input with
      | inl n => exact resolvedPreservesCoordinate_splitUniformImpl coordinate n
      | inr input => exact resolvedPreservesCoordinate_splitHashQuery coordinate (.ordinary input)

theorem materializedStartsPublished_of_mem_successful_sign
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublic : MaterializedStartsPublished context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (hsuccess : result.value.1 ≠ none) : MaterializedStartsPublished result.context := by
  rw [maskedPublishedChronologicalSign, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨digestOption, hdigest, hrest⟩ := hresult
  cases digestOption with
  | none => simp at hrest
  | some digest =>
      cases hselected : digest.value.1 with
      | none =>
          simp [hselected, runResolvedFromTable] at hrest
          subst result
          exact False.elim (hsuccess rfl)
      | some selected =>
          rcases selected with ⟨randomness, index, leaves⟩
          have hdigestPublic : MaterializedStartsPublished digest.context := by
            intro start hvalue
            have hpreserved := resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl start.coordinate _
              context fuel table cache digest hdigest
            exact hpreserved.2.mpr (hpublic start (by rwa [hpreserved.1] at hvalue))
          apply materializedStartsPublished_of_mem_successful_signAfterDigest parameter ftsSecret randomness index leaves
            digest.context digest.remaining digest.table digest.value.2 result hdigestPublic _ hsuccess
          simpa only [hselected] using hrest

theorem canonicalize_known_start_eq_of_materializedStartsPublished
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hpublic : MaterializedStartsPublished context) (hstarts : StartTableAgrees context.state table)
    (start : OtsSecretIndex) (hknown : context.state.values start.coordinate ≠ none) :
    (canonicalizeMaterializedValues table context).state.values start.coordinate = context.state.values start.coordinate := by
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hknown
  have hrevealed := hpublic start (by rw [houtput]; simp)
  have hagree := hstarts start output houtput
  change (if start.coordinate ∈ context.state.revealed then some (table start) else none) =
    context.state.values start.coordinate
  simp only [hrevealed, if_pos, houtput, hagree]

theorem successful_sign_canonicalization_preserves_known_starts
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hcanonical : CanonicalMaterializedValues table context) (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (hsuccess : result.value.1 ≠ none) (start : OtsSecretIndex)
    (hknown : result.context.state.values start.coordinate ≠ none) :
    (canonicalizeMaterializedValues table result.context).state.values start.coordinate = result.context.state.values start.coordinate := by
  have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
  exact canonicalize_known_start_eq_of_materializedStartsPublished table result.context
    (materializedStartsPublished_of_mem_successful_sign parameter root ftsSecret message context fuel table cache
      result (materializedStartsPublished_of_canonical table context hcanonical) hresult hsuccess)
    hcore.2.2 start hknown

theorem resolvedPreservesPublishedValues_revealPrivateLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    ResolvedPreservesPublished (revealPrivateLayerValues index lay encoding) := by
  unfold revealPrivateLayerValues
  exact (resolvedPreservesPublished_sequenceFin _ fun chainIdx =>
    resolvedPreservesPublishedValues_revealCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))).bind fun _ =>
          (resolvedPreservesPublished_sequenceFin _ fun level => by
            split
            · cases hlevelValue : level.val with
              | zero => exact resolvedPreservesPublishedValues_revealCoordinate _
              | succ current =>
                  rw [show current + 1 = Nat.succ current by omega]
                  change ResolvedPreservesPublished
                    (if hlevel : current < maxLayerHeight then
                      revealCoordinate (.position (.node lay (treeIndexAt index lay)
                        ⟨current, hlevel⟩ (leafOfNat
                          (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                    else pure 0)
                  by_cases hlevel : current < maxLayerHeight
                  · rw [dif_pos hlevel]
                    exact resolvedPreservesPublishedValues_revealCoordinate _
                  · rw [dif_neg hlevel]
                    exact ResolvedPreservesPublished.pure 0
            · exact ResolvedPreservesPublished.pure 0).bind fun _ =>
                  ResolvedPreservesPublished.pure _

theorem resolvedPreservesPublishedValues_maskedChronologicalSignLayer
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    ResolvedPreservesPublished (maskedChronologicalSignLayer parameter ftsSecret index lay) := by
  unfold maskedChronologicalSignLayer
  exact (resolvedPreservesPublishedValues_maskedSignLayer parameter ftsSecret index lay).bind fun selected =>
    match selected with
    | none => .pure none
    | some (_, encoding) =>
        (resolvedPreservesPublishedValues_revealPrivateLayerValues index lay encoding).bind fun _ => .pure _

theorem resolvedPreservesPublishedValues_maskedPublishedChronologicalSignAfterDigest
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    ResolvedPreservesPublished (maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves) := by
  rw [maskedPublishedChronologicalSignAfterDigest_eq]
  exact (resolvedPreservesPublishedValues_simulateQ_ordinaryHashImpl _).bind fun ftsPath =>
    (resolvedPreservesPublished_sequenceFin _ fun lay =>
      resolvedPreservesPublishedValues_maskedChronologicalSignLayer parameter ftsSecret index lay).bind fun layers =>
        resolvedPreservesPublishedValues_publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers

theorem resolvedPreservesPublishedValues_maskedPublishedChronologicalSign
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    ResolvedPreservesPublished (maskedPublishedChronologicalSign parameter root ftsSecret message) := by
  unfold maskedPublishedChronologicalSign
  exact (ResolvedPreservesPublished.of_preservesCoordinate fun coordinate =>
    resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl coordinate _).bind fun selected =>
      match selected with
      | none => .pure none
      | some (randomness, index, leaves) =>
          resolvedPreservesPublishedValues_maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves

theorem canonicalize_start_values_eq_of_materializedStartsPublished
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hpublic : MaterializedStartsPublished context) (hpublished : PublishedValues context.state)
    (hstarts : StartTableAgrees context.state table) (start : OtsSecretIndex) :
    (canonicalizeMaterializedValues table context).state.values start.coordinate = context.state.values start.coordinate := by
  by_cases hknown : context.state.values start.coordinate ≠ none
  · exact canonicalize_known_start_eq_of_materializedStartsPublished table context hpublic hstarts start hknown
  · have hmissing : context.state.values start.coordinate = none := not_not.mp hknown
    have hnot : start.coordinate ∉ context.state.revealed := fun h => hpublished start.coordinate h hmissing
    change (if start.coordinate ∈ context.state.revealed then some (table start) else none) =
      context.state.values start.coordinate
    simp [hnot, hmissing]

theorem successful_sign_canonicalization_preserves_start_values
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hcanonical : CanonicalMaterializedValues table context) (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (hsuccess : result.value.1 ≠ none) (start : OtsSecretIndex) :
    (canonicalizeMaterializedValues table result.context).state.values start.coordinate = result.context.state.values start.coordinate := by
  have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hresult
  exact canonicalize_start_values_eq_of_materializedStartsPublished table result.context
    (materializedStartsPublished_of_mem_successful_sign parameter root ftsSecret message context fuel table cache
      result (materializedStartsPublished_of_canonical table context hcanonical) hresult hsuccess)
    (resolvedPreservesPublishedValues_maskedPublishedChronologicalSign parameter root ftsSecret message
      context cache fuel table result hpublished hresult) hcore.2.2 start

theorem successful_sign_canonicalization_completedStartTable
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hcanonical : CanonicalMaterializedValues table context) (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (hsuccess : result.value.1 ≠ none) (base : OtsSecretIndex → HashOutput) :
    completedStartTable (canonicalizeMaterializedValues table result.context).state base =
      completedStartTable result.context.state base := by
  funext start
  unfold completedStartTable
  rw [successful_sign_canonicalization_preserves_start_values parameter root ftsSecret message context fuel table cache
    result hcanonical hconsistent hpublished hstarts hresult hsuccess start]

theorem successful_sign_canonicalization_historyHit
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hcanonical : CanonicalMaterializedValues table context) (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state) (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (hsuccess : result.value.1 ≠ none) (history : List Probe) (base : OtsSecretIndex → HashOutput) :
    ChainStartHistoryHit (canonicalizeMaterializedValues table result.context) history base =
      ChainStartHistoryHit result.context history base := by
  apply propext
  unfold ChainStartHistoryHit
  apply exists_congr
  rintro ⟨coordinate, digest⟩
  cases coordinate with
  | position position => simp [ChainStartEntryHit]
  | chainStart lay tree leafIdx chainIdx =>
      have heq := successful_sign_canonicalization_preserves_start_values parameter root ftsSecret message context fuel
        table cache result hcanonical hconsistent hpublished hstarts hresult hsuccess ⟨lay, tree, leafIdx, chainIdx⟩
      change (canonicalizeMaterializedValues table result.context).state.values (.chainStart lay tree leafIdx chainIdx) =
        result.context.state.values (.chainStart lay tree leafIdx chainIdx) at heq
      rw [heq]

theorem signing_start_erasure_requires_failed_reply
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hcanonical : CanonicalMaterializedValues table context) (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (start : OtsSecretIndex) (hknown : result.context.state.values start.coordinate ≠ none)
    (herased : (canonicalizeMaterializedValues table result.context).state.values start.coordinate = none) :
    result.value.1 = none := by
  by_contra hsuccess
  rw [successful_sign_canonicalization_preserves_known_starts parameter root ftsSecret message context fuel table cache
    result hcanonical hconsistent hstarts hresult hsuccess start hknown] at herased
  exact hknown herased

theorem signing_start_erasure_requires_failed_afterDigest
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublic : MaterializedStartsPublished context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)))
    (start : OtsSecretIndex) (hknown : result.context.state.values start.coordinate ≠ none)
    (herased : (canonicalizeMaterializedValues table result.context).state.values start.coordinate = none) :
    ∃ (digest : ResolvedRunResult (Option (Randomness × Index × (DigestTree → FtsLeaf)) × SplitHashCache))
      (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf),
      some digest ∈ support (runResolvedFromTable context fuel table
        ((simulateQ ordinaryRomImpl (signDigestLoop digestAttemptLimit
          ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).run cache)) ∧
      digest.value.1 = some (randomness, index, leaves) ∧
      some result ∈ support (runResolvedFromTable digest.context digest.remaining digest.table
        ((maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves).run digest.value.2)) ∧
      result.value.1 = none := by
  have hnotPublic : ¬MaterializedStartsPublished result.context := by
    intro h
    have hrevealed := h start hknown
    change (if start.coordinate ∈ result.context.state.revealed then some (table start) else none) = none at herased
    simp [hrevealed] at herased
  have hfailed : result.value.1 = none := by
    by_contra hsuccess
    exact hnotPublic (materializedStartsPublished_of_mem_successful_sign parameter root ftsSecret message
      context fuel table cache result hpublic hresult hsuccess)
  rw [maskedPublishedChronologicalSign, StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨digestOption, hdigest, hrest⟩ := hresult
  cases digestOption with
  | none => simp at hrest
  | some digest =>
      cases hselected : digest.value.1 with
      | none =>
          simp [hselected, runResolvedFromTable] at hrest
          subst result
          apply False.elim
          apply hnotPublic
          intro other hvalue
          have hpreserved := resolvedPreservesCoordinate_simulateQ_ordinaryRomImpl other.coordinate _
            context fuel table cache digest hdigest
          exact hpreserved.2.mpr (hpublic other (by rwa [hpreserved.1] at hvalue))
      | some selected =>
          rcases selected with ⟨randomness, index, leaves⟩
          exact ⟨digest, randomness, index, leaves, hdigest, hselected,
            by simpa only [hselected] using hrest, hfailed⟩

theorem canonicalize_completedStartTable_independent
    (context : DeferredContext) (left right : OtsSecretIndex → HashOutput)
    (hpublished : PublishedValues context.state) :
    canonicalizeMaterializedValues (completedStartTable context.state left) context =
      canonicalizeMaterializedValues (completedStartTable context.state right) context := by
  have hvalues : publicMaterializedValues (completedStartTable context.state left) context =
      publicMaterializedValues (completedStartTable context.state right) context := by
    funext coordinate
    unfold publicMaterializedValues
    by_cases hrevealed : coordinate ∈ context.state.revealed
    · simp only [hrevealed, if_pos]
      cases coordinate with
      | position position => rfl
      | chainStart lay tree leafIdx chainIdx =>
          obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hpublished _ hrevealed)
          simp [resolvedCompletionValue, completedStartTable, OtsSecretIndex.coordinate, houtput]
    · simp [hrevealed]
  unfold canonicalizeMaterializedValues
  rw [hvalues]

theorem completeResolvedHistory_canonicalize
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (value : α)
    (reference : OtsSecretIndex → HashOutput)
    (hpublic : MaterializedStartsPublished context) (hpublished : PublishedValues context.state) :
    (completeResolvedHistory context fuel history value >>= fun result =>
      pure (match result with
        | none => none
        | some result => some { result with context := canonicalizeMaterializedValues result.table result.context })) =
    completeResolvedHistory (canonicalizeMaterializedValues (completedStartTable context.state reference) context)
      fuel history value := by
  let after := canonicalizeMaterializedValues (completedStartTable context.state reference) context
  have hvalues : ∀ start : OtsSecretIndex, after.state.values start.coordinate = context.state.values start.coordinate :=
    canonicalize_start_values_eq_of_materializedStartsPublished _ context hpublic hpublished
      (startTableAgrees_completedStartTable context.state reference)
  have hhistory : ∀ base, ChainStartHistoryHit after history base = ChainStartHistoryHit context history base :=
    fun base => chainStartHistoryHit_eq_of_start_values_eq context after history base hvalues
  have htable : ∀ base, completedStartTable after.state base = completedStartTable context.state base := by
    intro base
    funext start
    unfold completedStartTable
    rw [hvalues]
  unfold completeResolvedHistory
  rw [bind_assoc]
  congr 1
  funext base
  rw [hhistory base]
  split_ifs
  · simp only [pure_bind]
  · simp only [pure_bind]
    rw [canonicalize_completedStartTable_independent context base reference hpublished, htable base]

end SphincsSecurity.Concrete.OtsProbeSimulation
