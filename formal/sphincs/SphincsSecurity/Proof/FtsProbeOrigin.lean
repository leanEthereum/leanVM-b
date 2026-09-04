import SphincsSecurity.Proof.FtsProbeAdversary

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec

def DetailedResult.mapValue (transform : alpha → beta) :
    DetailedResult Coordinate alpha → DetailedResult Coordinate beta
  | .stopped hit => .stopped hit
  | .done hit state value => .done hit state (transform value)

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem runDetailed_mapValue (table : Coordinate → Digest) (state : State Coordinate)
    (fuel : Nat) (computation : OracleComp (World Coordinate) alpha)
    (transform : alpha → beta) :
    runDetailed table state fuel (transform <$> computation) =
      DetailedResult.mapValue transform <$>
        runDetailed table state fuel computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runDetailed, DetailedResult.mapValue]
  | query_bind input next ih =>
      rw [map_bind]
      cases input with
      | uniform n =>
          rw [runDetailed_uniform_query_bind, runDetailed_uniform_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output state fuel
      | hashOutput =>
          rw [runDetailed_hashOutput_query_bind, runDetailed_hashOutput_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output state fuel
      | probe coordinate candidate =>
          rw [runDetailed_probe_query_bind, runDetailed_probe_query_bind]
          cases fuel with
          | zero => simp [DetailedResult.mapValue]
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | none => exact ih () (state.addPending coordinate candidate) remaining
              | some value => exact ih () state remaining
      | reveal coordinate =>
          rw [runDetailed_reveal_query_bind, runDetailed_reveal_query_bind]
          cases hrevealed : state.revealed coordinate with
          | some value => exact ih value state fuel
          | none =>
              by_cases hhit : table coordinate ∈ state.pending coordinate
              · simp [hhit, DetailedResult.mapValue]
              · simp only [hhit, ↓reduceIte]
                exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel

theorem mem_support_runDetailed_stateT_map
    (table : Coordinate → Digest) (state finalState : State Coordinate)
    (fuel : Nat)
    (computation : StateT sigma (OracleComp (World Coordinate)) alpha)
    (transform : alpha → beta) (hit : Bool) (value : beta) (finalSigma : sigma)
    (hresult : .done hit finalState (value, finalSigma) ∈ support
      (runDetailed table state fuel ((transform <$> computation).run initialSigma))) :
    ∃ source, transform source = value ∧
      .done hit finalState (source, finalSigma) ∈ support
        (runDetailed table state fuel (computation.run initialSigma)) := by
  rw [StateT.run_map, runDetailed_mapValue, support_map] at hresult
  obtain ⟨detailed, hdetailed, heq⟩ := hresult
  cases detailed with
  | stopped stoppedHit => simp [DetailedResult.mapValue] at heq
  | done sourceHit sourceState sourceValue =>
      simp only [DetailedResult.mapValue, DetailedResult.done.injEq] at heq
      obtain ⟨hhit, hstate, hvalue⟩ := heq
      subst sourceHit
      subst sourceState
      refine ⟨sourceValue.1, ?_, ?_⟩
      · exact congrArg Prod.fst hvalue
      · have hcache := congrArg Prod.snd hvalue
        change sourceValue.2 = finalSigma at hcache
        rw [← hcache]
        change .done hit finalState sourceValue ∈
          support (runDetailed table state fuel (computation.run initialSigma))
        exact hdetailed

end SphincsSecurity.AdaptiveRevealProbe

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

def SelectedCoordinate (index : Index) (leaves : DigestTree → FtsLeaf)
    (coordinate : Coordinate) : Prop :=
  coordinate.1 = index ∧ coordinate.2.2 = leaves (ftsIndexOf coordinate.2.1)

def RevealedOnlyFrom (initial final : AdaptiveRevealProbe.State Coordinate)
    (allowed : Coordinate → Prop) : Prop :=
  ∀ coordinate value, final.revealed coordinate = some value →
    initial.revealed coordinate = some value ∨ allowed coordinate

theorem signingTraceComputation_query_bind
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) alpha) :
    signingTraceComputation
        ((liftM ((OracleWorld + SigningSpec).query input) :
          OracleComp (OracleWorld + SigningSpec) _) >>= next) = (do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      (fun result => (result.1, signingLogFragment input output ++ result.2)) <$>
        signingTraceComputation (next output)) := by
  simp [signingTraceComputation]

theorem simulateQ_randomOracle_cache_le
    (computation : OracleComp HashSpec alpha) (initial final : QueryCache HashSpec)
    (value : alpha)
    (hresult : (value, final) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run initial)) :
    initial ≤ final := by
  exact OracleComp.simulateQ_run_preservesInv
    (randomOracle : QueryImpl HashSpec _)
    (fun cache => initial ≤ cache)
    (QueryImpl.PreservesInv.withCaching_le uniformSampleImpl initial)
    computation initial le_rfl (value, final) hresult

theorem simulateQ_unloggedMappedAdversaryImpl_cache_le
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initial final : QueryCache HashSpec) (value : alpha)
    (hresult : (value, final) ∈ support
      ((simulateQ (unloggedMappedAdversaryImpl secretKey) computation).run initial)) :
    initial ≤ final := by
  apply OracleComp.simulateQ_run_preservesInv
    (unloggedMappedAdversaryImpl secretKey) (fun cache => initial ≤ cache) _
    computation initial le_rfl (value, final) hresult
  intro input cache hle result hmem
  exact hle.trans (unloggedMappedAdversaryImpl_cache_le secretKey input cache result hmem)

def CoveredByLog (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (log : QueryLog SigningSpec) (coordinate : Coordinate) : Prop :=
  ∃ (message : Message) (signature : Signature) (index : Index)
      (leaves : DigestTree → FtsLeaf),
    (⟨message, some signature⟩ : SigningEntry) ∈ log
      ∧ SuccessfulDigestRun f cache secretKey message signature.randomness index leaves
      ∧ SelectedCoordinate index leaves coordinate

theorem CoveredByLog.mono_cache
    {f : QueryImpl HashSpec Id} {initial final : QueryCache HashSpec}
    {secretKey : SecretKey} {log : QueryLog SigningSpec} {coordinate : Coordinate}
    (hcovered : CoveredByLog f initial secretKey log coordinate)
    (hle : initial ≤ final) : CoveredByLog f final secretKey log coordinate := by
  obtain ⟨message, signature, index, leaves, hentry, hdigest, hcoordinate⟩ := hcovered
  exact ⟨message, signature, index, leaves, hentry,
    ⟨hdigest.1, hdigest.2.1, hdigest.2.2.mono hle⟩, hcoordinate⟩

theorem CoveredByLog.mono_log
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {left right : QueryLog SigningSpec} {coordinate : Coordinate}
    (hcovered : CoveredByLog f cache secretKey right coordinate) :
    CoveredByLog f cache secretKey (left ++ right) coordinate := by
  obtain ⟨message, signature, index, leaves, hentry, hdigest, hcoordinate⟩ := hcovered
  exact ⟨message, signature, index, leaves, List.mem_append_right left hentry,
    hdigest, hcoordinate⟩

theorem peel_signingTrace_tail
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (logPrefix : QueryLog SigningSpec)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (value : alpha) (log : QueryLog SigningSpec)
    (hresult : .done false finalState ((value, log), finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          ((fun result => (result.1, logPrefix ++ result.2)) <$>
            signingTraceComputation computation)).run cache))) :
    ∃ tailLog, log = logPrefix ++ tailLog ∧
      .done false finalState ((value, tailLog), finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state fuel
          ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
            (signingTraceComputation computation)).run cache)) := by
  rw [simulateQ_map] at hresult
  obtain ⟨source, hsource, htail⟩ :=
    AdaptiveRevealProbe.mem_support_runDetailed_stateT_map table state finalState fuel
      (simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
        (signingTraceComputation computation))
      (fun result => (result.1, logPrefix ++ result.2)) false
      (value, log) finalCache hresult
  rcases source with ⟨sourceValue, tailLog⟩
  have hvalue : sourceValue = value := congrArg Prod.fst hsource
  have hlog : logPrefix ++ tailLog = log := congrArg Prod.snd hsource
  subst sourceValue
  exact ⟨tailLog, hlog.symm, htail⟩


theorem revealedOnlyFrom_revealFtsSecret
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (coordinate : Coordinate) (value : Digest)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hhidden : ∃ output, cache (.hiddenLeaf coordinate) = some output)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((revealFtsSecret parameter coordinate).run cache))) :
    RevealedOnlyFrom state finalState (fun other => other = coordinate) := by
  cases hrevealed : state.revealed coordinate with
  | none =>
      obtain ⟨output, hhiddenCache⟩ := hhidden
      rw [runDetailed_revealFtsSecret_hidden parameter table state fuel cache coordinate output
        hrevealed hclean hhiddenCache] at hresult
      simp only [support_pure, Set.mem_singleton_iff,
        AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      obtain ⟨hfinalState, _⟩ := hresult.2
      subst finalState
      intro other otherValue hother
      by_cases heq : other = coordinate
      · exact Or.inr heq
      · exact Or.inl (by
          simpa [AdaptiveRevealProbe.State.install, Function.update_of_ne heq] using hother)
  | some revealedValue =>
      obtain ⟨hvalue, output, hhiddenCache, hordinaryCache⟩ :=
        hsynced coordinate revealedValue hrevealed
      rw [runDetailed_revealFtsSecret_revealed parameter table state fuel cache coordinate
        revealedValue output hrevealed hvalue hhiddenCache hordinaryCache hclean] at hresult
      simp only [support_pure, Set.mem_singleton_iff,
        AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      obtain ⟨hfinalState, _⟩ := hresult.2
      subst finalState
      intro other otherValue hother
      exact Or.inl hother

theorem RevealedOnlyFrom.trans
    {initial middle final : AdaptiveRevealProbe.State Coordinate}
    {left right : Coordinate → Prop}
    (hleft : RevealedOnlyFrom initial middle left)
    (hright : RevealedOnlyFrom middle final right) :
    RevealedOnlyFrom initial final (fun coordinate => left coordinate ∨ right coordinate) := by
  intro coordinate value hrevealed
  rcases hright coordinate value hrevealed with hmiddle | hright
  · rcases hleft coordinate value hmiddle with hinitial | hleft
    · exact Or.inl hinitial
    · exact Or.inr (Or.inl hleft)
  · exact Or.inr (Or.inr hright)

theorem hiddenLeaf_eq_of_mem_runDetailed_revealFtsSecret
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (coordinate : Coordinate) (value : Digest)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hhidden : ∃ output, cache (.hiddenLeaf coordinate) = some output)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((revealFtsSecret parameter coordinate).run cache))) :
    ∀ other, finalCache (.hiddenLeaf other) = cache (.hiddenLeaf other) := by
  cases hrevealed : state.revealed coordinate with
  | none =>
      obtain ⟨output, hhiddenCache⟩ := hhidden
      rw [runDetailed_revealFtsSecret_hidden parameter table state fuel cache coordinate output
        hrevealed hclean hhiddenCache] at hresult
      simp only [support_pure, Set.mem_singleton_iff,
        AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      have hcache : finalCache = Function.update cache
          (.ordinary (hiddenInput parameter table coordinate)) (some output) := by
        simpa using congrArg Prod.snd hresult.2.2
      intro other
      rw [hcache]
      simp
  | some revealedValue =>
      obtain ⟨hvalue, output, hhiddenCache, hordinaryCache⟩ :=
        hsynced coordinate revealedValue hrevealed
      rw [runDetailed_revealFtsSecret_revealed parameter table state fuel cache coordinate
        revealedValue output hrevealed hvalue hhiddenCache hordinaryCache hclean] at hresult
      simp only [support_pure, Set.mem_singleton_iff,
        AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      have hcache : finalCache = cache := by
        simpa using congrArg Prod.snd hresult.2.2
      intro other
      rw [hcache]

theorem revealedOnlyFrom_revealSequence {n : Nat}
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index)
    (coordinates : Fin n → Coordinate)
    (hcoordinates : ∀ position, (coordinates position).1 = index)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hcached : HiddenIndexCached index cache)
    (values : Fin n → Digest)
    (hresult : .done false finalState (values, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((sequenceFin fun position =>
          revealFtsSecret parameter (coordinates position)).run cache))) :
    RevealedOnlyFrom state finalState
      (fun coordinate => ∃ position, coordinate = coordinates position) := by
  induction n generalizing state cache finalState finalCache with
  | zero =>
      simp only [sequenceFin] at hresult
      simp [AdaptiveRevealProbe.runDetailed, hclean] at hresult
      obtain ⟨hstate, _⟩ := hresult
      subst finalState
      intro coordinate value hrevealed
      exact Or.inl hrevealed
  | succ n ih =>
      rw [sequenceFin, StateT.run_bind] at hresult
      obtain ⟨headState, headResult, hhead, hafterHead⟩ :=
        mem_support_runDetailed_bind_probeFree table state finalState fuel
          ((revealFtsSecret parameter (coordinates 0)).run cache) _
          (revealFtsSecret_probeFree parameter (coordinates 0) cache)
          hclean (values, finalCache) hresult
      rcases headResult with ⟨head, headCache⟩
      have hheadClean : AdaptiveRevealProbe.tableHits headState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table state headState fuel
          ((revealFtsSecret parameter (coordinates 0)).run cache)
          (revealFtsSecret_probeFree parameter (coordinates 0) cache)
          hclean (head, headCache) hhead
      have hheadSynced : RevealedSynced parameter table headState headCache :=
        revealedSynced_of_mem_runDetailed_revealFtsSecret parameter table state headState
          fuel cache headCache (coordinates 0) head hclean hsynced
          (by
            have h := hcached (coordinates 0).2.1 (coordinates 0).2.2
            rw [← hcoordinates 0] at h
            exact h)
          hhead
      have hheadOrigin := revealedOnlyFrom_revealFtsSecret parameter table state headState
        fuel cache headCache (coordinates 0) head hclean hsynced
        (by
          have h := hcached (coordinates 0).2.1 (coordinates 0).2.2
          rw [← hcoordinates 0] at h
          exact h)
        hhead
      rw [StateT.run_bind] at hafterHead
      obtain ⟨tailState, tailResult, htail, hfinish⟩ :=
        mem_support_runDetailed_bind_probeFree table headState finalState fuel
          ((sequenceFin fun position =>
            revealFtsSecret parameter (coordinates position.succ)).run headCache) _
          (sequenceFin_probeFree
            (fun position => revealFtsSecret parameter (coordinates position.succ))
            (fun position => revealFtsSecret_probeFree parameter
              (coordinates position.succ)) headCache)
          hheadClean (values, finalCache) hafterHead
      rcases tailResult with ⟨tail, tailCache⟩
      have hhiddenEq := hiddenLeaf_eq_of_mem_runDetailed_revealFtsSecret parameter table
        state headState fuel cache headCache (coordinates 0) head hclean hsynced
        (by
          have h := hcached (coordinates 0).2.1 (coordinates 0).2.2
          rw [← hcoordinates 0] at h
          exact h)
        hhead
      have htailCached : HiddenIndexCached index headCache := by
        intro tree leafIdx
        obtain ⟨output, houtput⟩ := hcached tree leafIdx
        exact ⟨output, (hhiddenEq (index, tree, leafIdx)).trans houtput⟩
      have htailOrigin := ih
        (coordinates := fun position => coordinates position.succ)
        (hcoordinates := fun position => hcoordinates position.succ)
        (state := headState) (finalState := tailState) (cache := headCache)
        (finalCache := tailCache) (values := tail)
        hheadClean hheadSynced htailCached htail
      have hparts := AdaptiveRevealProbe.DetailedResult.done.inj hfinish
      have hfinalState := hparts.2.1
      subst finalState
      intro coordinate value hrevealed
      rcases htailOrigin coordinate value hrevealed with hmiddle | ⟨position, hposition⟩
      · rcases hheadOrigin coordinate value hmiddle with hinitial | hzero
        · exact Or.inl hinitial
        · exact Or.inr ⟨0, hzero⟩
      · exact Or.inr ⟨position.succ, hposition⟩

theorem revealedOnlyFrom_revealSelectedFtsSecrets
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hcached : HiddenIndexCached index cache)
    (values : FtsTree → Digest)
    (hresult : .done false finalState (values, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((revealSelectedFtsSecrets parameter index leaves).run cache))) :
    RevealedOnlyFrom state finalState (SelectedCoordinate index leaves) := by
  unfold revealSelectedFtsSecrets at hresult
  have horigin := revealedOnlyFrom_revealSequence parameter table index
    (fun tree => (index, tree, leaves (ftsIndexOf tree))) (fun tree => rfl)
    state finalState fuel cache finalCache hclean hsynced hcached values hresult
  intro coordinate value hrevealed
  rcases horigin coordinate value hrevealed with hinitial | ⟨tree, htree⟩
  · exact Or.inl hinitial
  · subst coordinate
    exact Or.inr ⟨rfl, rfl⟩

set_option maxRecDepth 4000 in
theorem revealedOnlyFrom_maskedSignAfterDigest
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (signature : Option Signature)
    (hresult : .done false finalState (signature, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((maskedSignAfterDigest secretKey randomness index leaves).run cache))) :
    ∀ coordinate value, finalState.revealed coordinate = some value →
      state.revealed coordinate = some value ∨
        ∃ concrete, signature = some concrete ∧ concrete.randomness = randomness ∧
          SelectedCoordinate index leaves coordinate := by
  unfold maskedSignAfterDigest at hresult
  rw [StateT.run_bind] at hresult
  obtain ⟨pathState, pathResult, hpath, hafterPath⟩ :=
    mem_support_runDetailed_bind_probeFree table state finalState fuel
      ((maskedFtsOpen secretKey.parameter index leaves).run cache) _
      (maskedFtsOpen_probeFree secretKey.parameter index leaves cache) hclean
      (signature, finalCache) hresult
  rcases pathResult with ⟨ftsPath, pathCache⟩
  have hpathClean : AdaptiveRevealProbe.tableHits pathState table = false :=
    tableHits_false_of_mem_runDetailed_probeFree table state pathState fuel
      ((maskedFtsOpen secretKey.parameter index leaves).run cache)
      (maskedFtsOpen_probeFree secretKey.parameter index leaves cache) hclean
      (ftsPath, pathCache) hpath
  have hpathSynced : RevealedSynced secretKey.parameter table pathState pathCache :=
    revealedSynced_of_mem_runDetailed_stateFree secretKey.parameter table state pathState
      fuel cache pathCache ftsPath (maskedFtsOpen secretKey.parameter index leaves) hclean
      hsynced (maskedFtsOpen_stateFree secretKey.parameter index leaves)
      (maskedFtsOpen_cachePreserving secretKey.parameter index leaves) hpath
  have hpathState : pathState = state := by
    obtain ⟨raw, heq⟩ := AdaptiveRevealProbe.runDetailed_stateFree_support table state fuel
      ((maskedFtsOpen secretKey.parameter index leaves).run cache)
      (maskedFtsOpen_stateFree secretKey.parameter index leaves cache) hclean
      (.done false pathState (ftsPath, pathCache)) hpath
    exact (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1
  rw [StateT.run_bind] at hafterPath
  obtain ⟨layersState, layersResult, hlayers, hafterLayers⟩ :=
    mem_support_runDetailed_bind_probeFree table pathState finalState fuel
      ((sequenceFin fun lay => maskedSignLayer secretKey index lay).run pathCache) _
      (sequenceFin_probeFree (fun lay => maskedSignLayer secretKey index lay)
        (fun lay => maskedSignLayer_probeFree secretKey index lay) pathCache)
      hpathClean (signature, finalCache) hafterPath
  rcases layersResult with ⟨layers, layersCache⟩
  have hlayersClean : AdaptiveRevealProbe.tableHits layersState table = false :=
    tableHits_false_of_mem_runDetailed_probeFree table pathState layersState fuel
      ((sequenceFin fun lay => maskedSignLayer secretKey index lay).run pathCache)
      (sequenceFin_probeFree (fun lay => maskedSignLayer secretKey index lay)
        (fun lay => maskedSignLayer_probeFree secretKey index lay) pathCache)
      hpathClean (layers, layersCache) hlayers
  have hlayersSynced : RevealedSynced secretKey.parameter table layersState layersCache :=
    revealedSynced_of_mem_runDetailed_stateFree secretKey.parameter table pathState layersState
      fuel pathCache layersCache layers
      (sequenceFin fun lay => maskedSignLayer secretKey index lay) hpathClean hpathSynced
      (sequenceFin_stateFree (fun lay => maskedSignLayer secretKey index lay)
        (fun lay => maskedSignLayer_stateFree secretKey index lay))
      (sequenceFin_cachePreserving (fun lay => maskedSignLayer secretKey index lay)
        (fun lay => maskedSignLayer_cachePreserving secretKey index lay)) hlayers
  have hlayersState : layersState = pathState := by
    obtain ⟨raw, heq⟩ := AdaptiveRevealProbe.runDetailed_stateFree_support table pathState fuel
      ((sequenceFin fun lay => maskedSignLayer secretKey index lay).run pathCache)
      (sequenceFin_stateFree (fun lay => maskedSignLayer secretKey index lay)
        (fun lay => maskedSignLayer_stateFree secretKey index lay) pathCache)
      hpathClean (.done false layersState (layers, layersCache)) hlayers
    exact (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1
  have hlayersCached : HiddenIndexCached index layersCache :=
    hiddenIndexCached_of_mem_runDetailed_maskedSignLayers secretKey table pathState
      layersState fuel pathCache layersCache index layers hpathClean hlayers
  cases hparts : traverseOption layers with
  | none =>
      simp only [hparts] at hafterLayers
      simp [AdaptiveRevealProbe.runDetailed, hlayersClean] at hafterLayers
      obtain ⟨hstate, _, _⟩ := hafterLayers
      subst finalState
      intro coordinate value hrevealed
      exact Or.inl (by simpa [hlayersState, hpathState] using hrevealed)
  | some parts =>
      simp only [hparts, StateT.run_bind] at hafterLayers
      obtain ⟨selectedState, selectedResult, hselected, hfinish⟩ :=
        mem_support_runDetailed_bind_probeFree table layersState finalState fuel
          ((revealSelectedFtsSecrets secretKey.parameter index leaves).run layersCache) _
          (revealSelectedFtsSecrets_probeFree secretKey.parameter index leaves layersCache)
          hlayersClean (signature, finalCache) hafterLayers
      rcases selectedResult with ⟨selected, selectedCache⟩
      have horigin := revealedOnlyFrom_revealSelectedFtsSecrets secretKey.parameter table
        index leaves layersState selectedState fuel layersCache selectedCache hlayersClean
        hlayersSynced hlayersCached selected hselected
      have hselectedClean : AdaptiveRevealProbe.tableHits selectedState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table layersState selectedState fuel
          ((revealSelectedFtsSecrets secretKey.parameter index leaves).run layersCache)
          (revealSelectedFtsSecrets_probeFree secretKey.parameter index leaves layersCache)
          hlayersClean (selected, selectedCache) hselected
      simp [AdaptiveRevealProbe.runDetailed, hselectedClean] at hfinish
      obtain ⟨hstate, hsignature, _⟩ := hfinish
      subst finalState
      intro coordinate value hrevealed
      rcases horigin coordinate value hrevealed with hold | hselectedCoordinate
      · exact Or.inl (by simpa [hlayersState, hpathState] using hold)
      · refine Or.inr ⟨_, hsignature, rfl, hselectedCoordinate⟩

set_option maxRecDepth 10000 in
theorem revealedOnlyFrom_maskedSignWithView
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (message : Message)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (result : Option Signature × Option FewTimeView)
    (f : QueryImpl HashSpec Id)
    (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((maskedSignWithView secretKey message).run cache))) :
    ∀ coordinate value, finalState.revealed coordinate = some value →
      state.revealed coordinate = some value ∨
        ∃ concrete index leaves,
          result.1 = some concrete
            ∧ SuccessfulDigestRun f (mergedCache secretKey.parameter table finalCache)
              (secretKeyWithFtsTable secretKey table) message concrete.randomness index leaves
            ∧ SelectedCoordinate index leaves coordinate := by
  unfold maskedSignWithView at hresult
  rw [StateT.run_bind] at hresult
  obtain ⟨loopState, loopResult, hloop, hafterLoop⟩ :=
    mem_support_runDetailed_bind_probeFree table state finalState fuel
      ((simulateQ splitRomImpl
        (signDigestLoop digestAttemptLimit secretKey message)).run cache) _
      (simulateQ_splitRomImpl_probeFree
        (signDigestLoop digestAttemptLimit secretKey message) cache)
      hclean (result, finalCache) hresult
  rcases loopResult with ⟨selected, loopCache⟩
  have hloopClean : AdaptiveRevealProbe.tableHits loopState table = false :=
    tableHits_false_of_mem_runDetailed_probeFree table state loopState fuel
      ((simulateQ splitRomImpl
        (signDigestLoop digestAttemptLimit secretKey message)).run cache)
      (simulateQ_splitRomImpl_probeFree
        (signDigestLoop digestAttemptLimit secretKey message) cache)
      hclean (selected, loopCache) hloop
  have hloopSynced : RevealedSynced secretKey.parameter table loopState loopCache :=
    revealedSynced_of_mem_runDetailed_stateFree secretKey.parameter table state loopState
      fuel cache loopCache selected
      (simulateQ splitRomImpl (signDigestLoop digestAttemptLimit secretKey message))
      hclean hsynced
      (simulateQ_splitRomImpl_stateFree
        (signDigestLoop digestAttemptLimit secretKey message))
      (simulateQ_splitRomImpl_cachePreserving
        (signDigestLoop digestAttemptLimit secretKey message)) hloop
  have hloopState : loopState = state := by
    obtain ⟨raw, heq⟩ := AdaptiveRevealProbe.runDetailed_stateFree_support table state fuel
      ((simulateQ splitRomImpl
        (signDigestLoop digestAttemptLimit secretKey message)).run cache)
      (simulateQ_splitRomImpl_stateFree
        (signDigestLoop digestAttemptLimit secretKey message) cache)
      hclean (.done false loopState (selected, loopCache)) hloop
    exact (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1
  cases selected with
  | none =>
      simp [AdaptiveRevealProbe.runDetailed, hloopClean] at hafterLoop
      obtain ⟨hstate, _, _⟩ := hafterLoop
      subst finalState
      intro coordinate value hrevealed
      exact Or.inl (by simpa [hloopState] using hrevealed)
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      rw [StateT.run_bind] at hafterLoop
      obtain ⟨signatureState, signatureResult, hsignature, hfinish⟩ :=
        mem_support_runDetailed_bind_probeFree table loopState finalState fuel
          ((maskedSignAfterDigest secretKey randomness index leaves).run loopCache) _
          (maskedSignAfterDigest_probeFree secretKey randomness index leaves loopCache)
          hloopClean (result, finalCache) hafterLoop
      rcases signatureResult with ⟨signature, signatureCache⟩
      have hsignatureSynced :
          RevealedSynced secretKey.parameter table signatureState signatureCache :=
        revealedSynced_of_mem_runDetailed_maskedSignAfterDigest secretKey table loopState
          signatureState fuel loopCache signatureCache randomness index leaves hloopClean
          hloopSynced signature hsignature
      have horigin := revealedOnlyFrom_maskedSignAfterDigest secretKey table loopState
        signatureState fuel loopCache signatureCache randomness index leaves hloopClean
        hloopSynced signature hsignature
      have hsignatureClean : AdaptiveRevealProbe.tableHits signatureState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table loopState signatureState fuel
          ((maskedSignAfterDigest secretKey randomness index leaves).run loopCache)
          (maskedSignAfterDigest_probeFree secretKey randomness index leaves loopCache)
          hloopClean (signature, signatureCache) hsignature
      simp [AdaptiveRevealProbe.runDetailed, hsignatureClean] at hfinish
      obtain ⟨hstate, hvalue, hcache⟩ := hfinish
      subst finalState
      subst finalCache
      intro coordinate value hrevealed
      rcases horigin coordinate value hrevealed with hold |
          ⟨concrete, hsignatureSome, hrandomness, hcoordinate⟩
      · exact Or.inl (by simpa [hloopState] using hold)
      · have hafterActual := CoupledAt.mem_support_ordinary
          (parameter := secretKey.parameter) (table := table) (state := loopState)
          (fuel := fuel)
          (masked := maskedSignAfterDigest secretKey randomness index leaves)
          (ordinary := simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAfterDigest (secretKeyWithFtsTable secretKey table)
              randomness index leaves))
          (cache := loopCache) (finalState := signatureState)
          (finalCache := signatureCache) (value := signature)
          (coupledAt_maskedSignAfterDigest secretKey table loopState fuel loopCache
            randomness index leaves hloopClean hloopSynced)
          hsignature
        have hle : mergedCache secretKey.parameter table loopCache ≤
            mergedCache secretKey.parameter table signatureCache :=
          simulateQ_randomOracle_cache_le
            (signAfterDigest (secretKeyWithFtsTable secretKey table)
              randomness index leaves)
            (mergedCache secretKey.parameter table loopCache)
            (mergedCache secretKey.parameter table signatureCache) signature hafterActual
        have hloopActualBase := CoupledAt.mem_support_ordinary
          (parameter := secretKey.parameter) (table := table) (state := state)
          (fuel := fuel)
          (masked := simulateQ splitRomImpl
            (signDigestLoop digestAttemptLimit secretKey message))
          (ordinary := simulateQ romImpl
            (signDigestLoop digestAttemptLimit secretKey message))
          (cache := cache) (finalState := loopState) (finalCache := loopCache)
          (value := some (randomness, index, leaves))
          ((coupled_simulateQ_splitRomImpl secretKey.parameter table state fuel
            (signDigestLoop digestAttemptLimit secretKey message) hclean
            (romOrdinaryOnly_signDigestLoop digestAttemptLimit secretKey table message)).coupledAt
              cache)
          hloop
        have hloopActual : (some (randomness, index, leaves),
              mergedCache secretKey.parameter table loopCache) ∈ support
            ((simulateQ romImpl
              (signDigestLoop digestAttemptLimit
                (secretKeyWithFtsTable secretKey table) message)).run
              (mergedCache secretKey.parameter table cache)) := by
          rw [signDigestLoop_secretKeyWithFtsTable]
          exact hloopActualBase
        have hloopReplay := replayRom_of_mem_support
          (signDigestLoop digestAttemptLimit
            (secretKeyWithFtsTable secretKey table) message)
          (mergedCache secretKey.parameter table cache)
          (some (randomness, index, leaves))
          (mergedCache secretKey.parameter table loopCache)
          hloopActual f (fun input output hcached => hf (hle hcached))
        have hdigest := successfulDigestLoop_of_mem_support f
          (secretKeyWithFtsTable secretKey table) message digestAttemptLimit
          randomness index leaves
          (mergedCache secretKey.parameter table cache)
          (mergedCache secretKey.parameter table loopCache)
          (mergedCache secretKey.parameter table signatureCache)
          hloopReplay hle hf
        refine Or.inr ⟨concrete, index, leaves, ?_, ?_, hcoordinate⟩
        · simpa [hvalue] using hsignatureSome
        · simpa [hrandomness] using hdigest

set_option maxRecDepth 10000 in
theorem revealedOnlyFrom_maskedSigningImpl
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (message : Message)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (signature : Option Signature)
    (f : QueryImpl HashSpec Id)
    (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hresult : .done false finalState (signature, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((maskedSigningImpl secretKey message).run cache))) :
    ∀ coordinate value, finalState.revealed coordinate = some value →
      state.revealed coordinate = some value ∨
        ∃ concrete index leaves,
          signature = some concrete
            ∧ SuccessfulDigestRun f (mergedCache secretKey.parameter table finalCache)
              (secretKeyWithFtsTable secretKey table) message concrete.randomness index leaves
            ∧ SelectedCoordinate index leaves coordinate := by
  unfold maskedSigningImpl at hresult
  rw [StateT.run_map] at hresult
  change .done false finalState (signature, finalCache) ∈ support
    (AdaptiveRevealProbe.runDetailed table state fuel
      (((fun result : Option Signature × Option FewTimeView => result.1) <$>
        maskedSignWithView secretKey message).run cache)) at hresult
  rw [StateT.run_map, map_eq_bind_pure_comp,
    AdaptiveRevealProbe.runDetailed_bind_probeFree table state fuel
      ((maskedSignWithView secretKey message).run cache) _
      (maskedSignWithView_probeFree secretKey message cache), mem_support_bind_iff] at hresult
  obtain ⟨viewResult, hviewResult, hfinish⟩ := hresult
  obtain ⟨viewState, viewValue, heq, hviewClean⟩ :=
    AdaptiveRevealProbe.runDetailed_probeFree_support table state fuel
      ((maskedSignWithView secretKey message).run cache)
      (maskedSignWithView_probeFree secretKey message cache) hclean viewResult hviewResult
  subst viewResult
  simp [AdaptiveRevealProbe.runDetailed, hviewClean] at hfinish
  obtain ⟨hstate, hvalue, hcache⟩ := hfinish
  subst finalState
  subst finalCache
  have horigin := revealedOnlyFrom_maskedSignWithView secretKey table state viewState fuel
    cache viewValue.2 message hclean hsynced viewValue.1 f hf hviewResult
  intro coordinate value hrevealed
  rcases horigin coordinate value hrevealed with hold |
      ⟨concrete, index, leaves, hsome, hdigest, hcoordinate⟩
  · exact Or.inl hold
  · refine Or.inr ⟨concrete, index, leaves, ?_, hdigest, hcoordinate⟩
    simpa [hvalue] using hsome

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 20000 in
theorem revealedOnlyFrom_signingTraceComputation
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (value : alpha) (log : QueryLog SigningSpec)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (f : QueryImpl HashSpec Id)
    (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hresult : .done false finalState ((value, log), finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          (signingTraceComputation computation)).run cache))) :
    RevealedOnlyFrom state finalState
      (CoveredByLog f (mergedCache secretKey.parameter table finalCache)
        (secretKeyWithFtsTable secretKey table) log) := by
  induction computation using OracleComp.inductionOn generalizing
      state fuel cache finalState finalCache value log with
  | pure result =>
      simp [signingTraceComputation, simulateQ_pure,
        AdaptiveRevealProbe.runDetailed, hclean] at hresult
      obtain ⟨hstate, hvalue, hlog, hcache⟩ := hresult
      subst finalState
      obtain ⟨hvalue, hlog'⟩ := hvalue
      subst value
      subst log
      intro coordinate revealedValue hrevealed
      exact Or.inl hrevealed
  | query_bind input next ih =>
      rw [signingTraceComputation_query_bind, simulateQ_bind, StateT.run_bind] at hresult
      cases input with
      | inl worldInput =>
          cases worldInput with
          | inl n =>
              obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
                mem_support_runDetailed_bind_probeFree table state finalState fuel
                  ((splitUniformImpl n).run cache)
                  (fun result =>
                    (simulateQ
                      (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                      ((fun tail => (tail.1,
                        signingLogFragment (.inl (.inl n)) result.1 ++ tail.2)) <$>
                        signingTraceComputation (next result.1))).run result.2)
                  (splitUniformImpl_probeFree n cache) hclean
                  ((value, log), finalCache) (by
                    simpa [maskedExpandedAdversaryImpl, probingRomImpl,
                      probingHashImpl] using hresult)
              rcases queryResult with ⟨output, queryCache⟩
              have hstep := maskedExpandedAdversaryImpl_done_false secretKey table state
                queryState fuel cache queryCache (.inl (.inl n)) output hclean hsynced hquery
              obtain ⟨tailLog, hlog, htailResult⟩ := peel_signingTrace_tail secretKey table
                (next output) (signingLogFragment (.inl (.inl n)) output)
                queryState finalState fuel queryCache finalCache value log hrest
              have htail := ih output queryState finalState fuel queryCache finalCache value
                tailLog hstep.2.1 hstep.2.2 hf htailResult
              have hqueryState : queryState = state := by
                obtain ⟨raw, heq⟩ := AdaptiveRevealProbe.runDetailed_stateFree_support
                  table state fuel ((splitUniformImpl n).run cache)
                  (splitUniformImpl_stateFree n cache) hclean
                  (.done false queryState (output, queryCache)) hquery
                exact (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1
              intro coordinate revealedValue hrevealed
              rcases htail coordinate revealedValue hrevealed with hold | hcovered
              · exact Or.inl (by simpa [hqueryState] using hold)
              · rw [hlog]
                exact Or.inr hcovered.mono_log
          | inr hashInput =>
              have hhashResult : .done false finalState ((value, log), finalCache) ∈ support
                  (AdaptiveRevealProbe.runDetailed table state fuel
                    ((probingHashQuery secretKey.parameter hashInput).run cache >>= fun result =>
                      (simulateQ
                        (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                        ((fun tail => (tail.1,
                          signingLogFragment (.inl (.inr hashInput)) result.1 ++ tail.2)) <$>
                          signingTraceComputation (next result.1))).run result.2)) := by
                simpa [maskedExpandedAdversaryImpl, probingRomImpl,
                  probingHashImpl] using hresult
              cases hdecode : decodeProbe? secretKey.parameter hashInput with
              | none =>
                  have hhashProbeFree : ProbeFree
                      (probingHashQuery secretKey.parameter hashInput) := by
                    intro workingCache
                    rw [probingHashQuery_run_eq, hdecode]
                    exact splitHashQuery_probeFree (.ordinary hashInput) workingCache
                  obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
                    mem_support_runDetailed_bind_probeFree table state finalState fuel
                      ((probingHashQuery secretKey.parameter hashInput).run cache)
                      (fun result =>
                        (simulateQ
                          (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                          ((fun tail => (tail.1,
                            signingLogFragment (.inl (.inr hashInput)) result.1 ++ tail.2)) <$>
                            signingTraceComputation (next result.1))).run result.2)
                      (hhashProbeFree cache) hclean ((value, log), finalCache) hhashResult
                  rcases queryResult with ⟨output, queryCache⟩
                  have hstep := maskedExpandedAdversaryImpl_done_false secretKey table state
                    queryState fuel cache queryCache (.inl (.inr hashInput)) output hclean
                    hsynced hquery
                  obtain ⟨tailLog, hlog, htailResult⟩ := peel_signingTrace_tail secretKey table
                    (next output) (signingLogFragment (.inl (.inr hashInput)) output)
                    queryState finalState fuel queryCache finalCache value log hrest
                  have htail := ih output queryState finalState fuel queryCache finalCache value
                    tailLog hstep.2.1 hstep.2.2 hf htailResult
                  have hrevealedEq := (probingHashQuery_done_false_invariants
                    secretKey.parameter table state queryState fuel cache queryCache
                    hashInput output hclean hquery).2
                  intro coordinate revealedValue hrevealed
                  rcases htail coordinate revealedValue hrevealed with hold | hcovered
                  · exact Or.inl (by simpa [hrevealedEq] using hold)
                  · rw [hlog]
                    exact Or.inr hcovered.mono_log
              | some probe =>
                  rw [probingHashQuery_run_eq, hdecode] at hhashResult
                  change .done false finalState ((value, log), finalCache) ∈ support
                    (AdaptiveRevealProbe.runDetailed table state fuel
                      ((liftM (OracleSpec.query
                        (spec := AdaptiveRevealProbe.World Coordinate)
                        (.probe (probe.index, probe.tree, probe.leafIdx) probe.candidate)) :
                          OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
                        (splitHashQuery (.ordinary hashInput)).run cache >>= fun result =>
                          (simulateQ
                            (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                            ((fun tail => (tail.1,
                              signingLogFragment (.inl (.inr hashInput)) result.1 ++ tail.2)) <$>
                              signingTraceComputation (next result.1))).run result.2)) at hhashResult
                  rw [AdaptiveRevealProbe.runDetailed_probe_query_bind] at hhashResult
                  cases fuel with
                  | zero => simp at hhashResult
                  | succ remaining =>
                      cases hrevealed : state.revealed
                          (probe.index, probe.tree, probe.leafIdx) with
                      | none =>
                          simp only [hrevealed] at hhashResult
                          by_cases hhit : table (probe.index, probe.tree, probe.leafIdx) =
                              probe.candidate
                          · have hpostClean := tableHits_false_of_mem_runDetailed_done_false
                                table
                                (state.addPending
                                  (probe.index, probe.tree, probe.leafIdx) probe.candidate)
                                finalState remaining
                                ((splitHashQuery (.ordinary hashInput)).run cache >>= fun result =>
                                  (simulateQ
                                    (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                                    ((fun tail => (tail.1,
                                      signingLogFragment (.inl (.inr hashInput)) result.1 ++
                                        tail.2)) <$>
                                      signingTraceComputation (next result.1))).run result.2)
                                ((value, log), finalCache) hhashResult
                            have hpostHit := AdaptiveRevealProbe.tableHits_addPending_eq_true
                              state table (probe.index, probe.tree, probe.leafIdx)
                              probe.candidate hhit
                            rw [hpostHit] at hpostClean
                            simp at hpostClean
                          · have hpostClean := AdaptiveRevealProbe.tableHits_addPending_eq_false
                                state table (probe.index, probe.tree, probe.leafIdx)
                                probe.candidate hclean hhit
                            obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
                              mem_support_runDetailed_bind_probeFree table
                                (state.addPending
                                  (probe.index, probe.tree, probe.leafIdx) probe.candidate)
                                finalState remaining
                                ((splitHashQuery (.ordinary hashInput)).run cache)
                                (fun result =>
                                  (simulateQ
                                    (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                                    ((fun tail => (tail.1,
                                      signingLogFragment (.inl (.inr hashInput)) result.1 ++
                                        tail.2)) <$>
                                      signingTraceComputation (next result.1))).run result.2)
                                (splitHashQuery_probeFree (.ordinary hashInput) cache)
                                hpostClean ((value, log), finalCache) hhashResult
                            rcases queryResult with ⟨output, queryCache⟩
                            have hqueryOriginal : .done false queryState
                                (output, queryCache) ∈ support
                                (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                                  ((probingHashQuery secretKey.parameter hashInput).run cache)) := by
                              rw [probingHashQuery_run_eq, hdecode]
                              change .done false queryState (output, queryCache) ∈ support
                                (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                                  ((liftM (OracleSpec.query
                                    (spec := AdaptiveRevealProbe.World Coordinate)
                                    (.probe (probe.index, probe.tree, probe.leafIdx)
                                      probe.candidate)) :
                                      OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>=
                                    fun _ =>
                                      (splitHashQuery (.ordinary hashInput)).run cache))
                              rw [AdaptiveRevealProbe.runDetailed_probe_query_bind, hrevealed]
                              exact hquery
                            have hstep := maskedExpandedAdversaryImpl_done_false secretKey table
                              state queryState (remaining + 1) cache queryCache
                              (.inl (.inr hashInput)) output hclean hsynced hqueryOriginal
                            obtain ⟨tailLog, hlog, htailResult⟩ := peel_signingTrace_tail
                              secretKey table (next output)
                              (signingLogFragment (.inl (.inr hashInput)) output)
                              queryState finalState remaining queryCache finalCache value log hrest
                            have htail := ih output queryState finalState remaining queryCache
                              finalCache value tailLog hstep.2.1 hstep.2.2 hf htailResult
                            have hrevealedEq := (probingHashQuery_done_false_invariants
                              secretKey.parameter table state queryState (remaining + 1)
                              cache queryCache hashInput output hclean hqueryOriginal).2
                            intro coordinate revealedValue hfinalRevealed
                            rcases htail coordinate revealedValue hfinalRevealed with
                              hold | hcovered
                            · exact Or.inl (by simpa [hrevealedEq] using hold)
                            · rw [hlog]
                              exact Or.inr hcovered.mono_log
                      | some revealedValue =>
                          simp only [hrevealed] at hhashResult
                          obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
                            mem_support_runDetailed_bind_probeFree table state finalState
                              remaining ((splitHashQuery (.ordinary hashInput)).run cache)
                              (fun result =>
                                (simulateQ
                                  (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                                  ((fun tail => (tail.1,
                                    signingLogFragment (.inl (.inr hashInput)) result.1 ++
                                      tail.2)) <$>
                                    signingTraceComputation (next result.1))).run result.2)
                              (splitHashQuery_probeFree (.ordinary hashInput) cache)
                              hclean ((value, log), finalCache) hhashResult
                          rcases queryResult with ⟨output, queryCache⟩
                          have hqueryOriginal : .done false queryState
                              (output, queryCache) ∈ support
                              (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                                ((probingHashQuery secretKey.parameter hashInput).run cache)) := by
                            rw [probingHashQuery_run_eq, hdecode]
                            change .done false queryState (output, queryCache) ∈ support
                              (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                                ((liftM (OracleSpec.query
                                  (spec := AdaptiveRevealProbe.World Coordinate)
                                  (.probe (probe.index, probe.tree, probe.leafIdx)
                                    probe.candidate)) :
                                    OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>=
                                  fun _ =>
                                    (splitHashQuery (.ordinary hashInput)).run cache))
                            rw [AdaptiveRevealProbe.runDetailed_probe_query_bind, hrevealed]
                            exact hquery
                          have hstep := maskedExpandedAdversaryImpl_done_false secretKey table
                            state queryState (remaining + 1) cache queryCache
                            (.inl (.inr hashInput)) output hclean hsynced hqueryOriginal
                          obtain ⟨tailLog, hlog, htailResult⟩ := peel_signingTrace_tail
                            secretKey table (next output)
                            (signingLogFragment (.inl (.inr hashInput)) output)
                            queryState finalState remaining queryCache finalCache value log hrest
                          have htail := ih output queryState finalState remaining queryCache
                            finalCache value tailLog hstep.2.1 hstep.2.2 hf htailResult
                          have hrevealedEq := (probingHashQuery_done_false_invariants
                            secretKey.parameter table state queryState (remaining + 1)
                            cache queryCache hashInput output hclean hqueryOriginal).2
                          intro coordinate finalValue hfinalRevealed
                          rcases htail coordinate finalValue hfinalRevealed with hold | hcovered
                          · exact Or.inl (by simpa [hrevealedEq] using hold)
                          · rw [hlog]
                            exact Or.inr hcovered.mono_log
      | inr message =>
          have hsignProbeFree : ProbeFree (maskedSigningImpl secretKey message) := by
            unfold maskedSigningImpl
            exact (maskedSignWithView_probeFree secretKey message).map Prod.fst
          obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
            mem_support_runDetailed_bind_probeFree table state finalState fuel
              ((maskedSigningImpl secretKey message).run cache)
              (fun result =>
                (simulateQ
                  (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                  ((fun tail => (tail.1,
                    signingLogFragment (.inr message) result.1 ++ tail.2)) <$>
                    signingTraceComputation (next result.1))).run result.2)
              (hsignProbeFree cache) hclean ((value, log), finalCache) (by
                simpa [maskedExpandedAdversaryImpl, probingRomImpl,
                  probingHashImpl] using hresult)
          rcases queryResult with ⟨output, queryCache⟩
          have hstep := maskedExpandedAdversaryImpl_done_false secretKey table state
            queryState fuel cache queryCache (.inr message) output hclean hsynced hquery
          obtain ⟨tailLog, hlog, htailResult⟩ := peel_signingTrace_tail secretKey table
            (next output) (signingLogFragment (.inr message) output)
            queryState finalState fuel queryCache finalCache value log hrest
          have htail := ih output queryState finalState fuel queryCache finalCache value
            tailLog hstep.2.1 hstep.2.2 hf htailResult
          have htailActual := simulateQ_maskedExpandedAdversaryImpl_done_false secretKey table
            (signingTraceComputation (next output)) queryState finalState fuel queryCache
            finalCache (value, tailLog) hstep.2.1 hstep.2.2 htailResult
          have hle : mergedCache secretKey.parameter table queryCache ≤
              mergedCache secretKey.parameter table finalCache :=
            simulateQ_unloggedMappedAdversaryImpl_cache_le
              (secretKeyWithFtsTable secretKey table)
              (signingTraceComputation (next output))
              (mergedCache secretKey.parameter table queryCache)
              (mergedCache secretKey.parameter table finalCache)
              (value, tailLog) htailActual.1
          have hqueryOrigin := revealedOnlyFrom_maskedSigningImpl secretKey table state
            queryState fuel cache queryCache message hclean hsynced output f
            (fun input answer hcached => hf (hle hcached)) hquery
          intro coordinate revealedValue hfinalRevealed
          rcases htail coordinate revealedValue hfinalRevealed with hqueryRevealed | hcovered
          · rcases hqueryOrigin coordinate revealedValue hqueryRevealed with
              hinitial | ⟨signature, index, leaves, houtput, hdigest, hcoordinate⟩
            · exact Or.inl hinitial
            · rw [hlog]
              refine Or.inr ⟨message, signature, index, leaves, ?_, ?_, hcoordinate⟩
              · simp [signingLogFragment, houtput]
              · exact ⟨hdigest.1, hdigest.2.1, hdigest.2.2.mono hle⟩
          · rw [hlog]
            exact Or.inr hcovered.mono_log

theorem signedFtsLeaf_of_signing_entry_selected
    (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initialCache : QueryCache HashSpec) (value : alpha)
    (signingLog : QueryLog SigningSpec) (adversaryCache finalCache : QueryCache HashSpec)
    (hmem : ((value, signingLog), adversaryCache) ∈ support
      ((simulateQ romImpl
        ((simulateQ (forwardOracles + signingOracle scheme secretKey)
          computation).run)).run initialCache))
    (hle : adversaryCache ≤ finalCache) (hf : finalCache.AgreesWithFn f)
    (message : Message) (signature : Signature) (index : Index)
    (leaves : DigestTree → FtsLeaf) (coordinate : Coordinate)
    (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ signingLog)
    (hdigest : SuccessfulDigestRun f finalCache secretKey message signature.randomness
      index leaves)
    (hselected : SelectedCoordinate index leaves coordinate) :
    SignedFtsLeaf f finalCache secretKey signingLog coordinate.1 coordinate.2.1
      coordinate.2.2 := by
  have hrun := successfulSignRun_of_signing_entry f secretKey computation initialCache value
    signingLog adversaryCache finalCache hmem hle hf
    (⟨message, some signature⟩ : SigningEntry) signature rfl hentry
  obtain ⟨actualIndex, actualLeaves, hhonest⟩ := hrun.honest_fts_at
  have hselection : (actualIndex, actualLeaves) = (index, leaves) := by
    apply Option.some.inj
    exact hhonest.1.2.1.symm.trans hdigest.2.1
  have hindex : actualIndex = index := congrArg Prod.fst hselection
  have hleaves : actualLeaves = leaves := congrArg Prod.snd hselection
  subst actualIndex
  subst actualLeaves
  rw [hselected.1]
  refine ⟨⟨message, some signature⟩, signature, leaves, hentry, rfl, hrun,
    hhonest, ?_⟩
  exact hselected.2.symm

theorem simulateQ_unloggedMapped_signingTraceComputation
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    simulateQ (unloggedMappedAdversaryImpl secretKey)
        (signingTraceComputation computation) =
      simulateQ romImpl
        ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) := by
  rw [← simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    ← writerTMapBase_expanded_withTraceAppend_eq_unlogged,
    ← QueryImpl.simulateQ_writerTMapBase_run,
    ← forwardOracles_add_signingOracle_eq_withTraceAppend]

theorem CoveredByLog.signedFtsLeaf
    {f : QueryImpl HashSpec Id} {secretKey : SecretKey}
    {computation : OracleComp (OracleWorld + SigningSpec) alpha}
    {initialCache : QueryCache HashSpec} {value : alpha}
    {signingLog : QueryLog SigningSpec} {adversaryCache finalCache : QueryCache HashSpec}
    {coordinate : Coordinate}
    (hcovered : CoveredByLog f finalCache secretKey signingLog coordinate)
    (hmem : ((value, signingLog), adversaryCache) ∈ support
      ((simulateQ romImpl
        ((simulateQ (forwardOracles + signingOracle scheme secretKey)
          computation).run)).run initialCache))
    (hle : adversaryCache ≤ finalCache) (hf : finalCache.AgreesWithFn f) :
    SignedFtsLeaf f finalCache secretKey signingLog coordinate.1 coordinate.2.1
      coordinate.2.2 := by
  obtain ⟨message, signature, index, leaves, hentry, hdigest, hselected⟩ := hcovered
  exact signedFtsLeaf_of_signing_entry_selected f secretKey computation initialCache value
    signingLog adversaryCache finalCache hmem hle hf message signature index leaves coordinate
    hentry hdigest hselected

set_option maxRecDepth 20000 in
theorem signedFtsLeaf_of_revealed_signingTraceComputation
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (fuel : Nat) (initialCache finalCache : SplitHashCache)
    (finalState : AdaptiveRevealProbe.State Coordinate)
    (value : alpha) (log : QueryLog SigningSpec)
    (hsynced : RevealedSynced secretKey.parameter table
      AdaptiveRevealProbe.State.empty initialCache)
    (f : QueryImpl HashSpec Id)
    (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (hresult : .done false finalState ((value, log), finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty fuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          (signingTraceComputation computation)).run initialCache)))
    (coordinate : Coordinate) (revealedValue : Digest)
    (hrevealed : finalState.revealed coordinate = some revealedValue) :
    SignedFtsLeaf f (mergedCache secretKey.parameter table finalCache)
      (secretKeyWithFtsTable secretKey table) log coordinate.1 coordinate.2.1
      coordinate.2.2 := by
  have hinitialClean : AdaptiveRevealProbe.tableHits
      (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = false := by
    simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]
  have horigin := revealedOnlyFrom_signingTraceComputation secretKey table computation
    AdaptiveRevealProbe.State.empty finalState fuel initialCache finalCache value log
    hinitialClean hsynced f hf hresult
  rcases horigin coordinate revealedValue hrevealed with hinitial | hcovered
  · simp [AdaptiveRevealProbe.State.empty] at hinitial
  · have hactual := simulateQ_maskedExpandedAdversaryImpl_done_false secretKey table
      (signingTraceComputation computation) AdaptiveRevealProbe.State.empty finalState fuel
      initialCache finalCache (value, log) hinitialClean hsynced hresult
    rw [simulateQ_unloggedMapped_signingTraceComputation] at hactual
    exact hcovered.signedFtsLeaf hactual.1 le_rfl hf

set_option maxRecDepth 20000 in
theorem signedFtsLeaf_of_revealed_signingTraceComputation_at_reference
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (fuel : Nat) (initialCache finalCache : SplitHashCache)
    (finalState : AdaptiveRevealProbe.State Coordinate)
    (value : alpha) (log : QueryLog SigningSpec)
    (hsynced : RevealedSynced secretKey.parameter table
      AdaptiveRevealProbe.State.empty initialCache)
    (referenceCache : QueryCache HashSpec)
    (hle : mergedCache secretKey.parameter table finalCache ≤ referenceCache)
    (f : QueryImpl HashSpec Id) (hf : referenceCache.AgreesWithFn f)
    (hresult : .done false finalState ((value, log), finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty fuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          (signingTraceComputation computation)).run initialCache)))
    (coordinate : Coordinate) (revealedValue : Digest)
    (hrevealed : finalState.revealed coordinate = some revealedValue) :
    SignedFtsLeaf f referenceCache (secretKeyWithFtsTable secretKey table) log
      coordinate.1 coordinate.2.1 coordinate.2.2 := by
  have hinitialClean : AdaptiveRevealProbe.tableHits
      (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = false := by
    simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]
  have horigin := revealedOnlyFrom_signingTraceComputation secretKey table computation
    AdaptiveRevealProbe.State.empty finalState fuel initialCache finalCache value log
    hinitialClean hsynced f (fun input output hcached => hf (hle hcached)) hresult
  rcases horigin coordinate revealedValue hrevealed with hinitial | hcovered
  · simp [AdaptiveRevealProbe.State.empty] at hinitial
  · have hactual := simulateQ_maskedExpandedAdversaryImpl_done_false secretKey table
      (signingTraceComputation computation) AdaptiveRevealProbe.State.empty finalState fuel
      initialCache finalCache (value, log) hinitialClean hsynced hresult
    rw [simulateQ_unloggedMapped_signingTraceComputation] at hactual
    exact (hcovered.mono_cache hle).signedFtsLeaf hactual.1 hle hf

end SphincsSecurity.Concrete.FtsProbeSimulation
