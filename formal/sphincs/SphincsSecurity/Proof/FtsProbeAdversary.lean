import SphincsSecurity.Proof.FtsProbeSigner
import SphincsSecurity.Proof.SecretProbeTerminal

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

theorem tableHits_eq_false_of_addPending_eq_false
    (state : AdaptiveRevealProbe.State Coordinate) (table : Coordinate → Digest)
    (coordinate : Coordinate) (candidate : Digest)
    (hclean : AdaptiveRevealProbe.tableHits
      (state.addPending coordinate candidate) table = false) :
    AdaptiveRevealProbe.tableHits state table = false := by
  classical
  unfold AdaptiveRevealProbe.tableHits at hclean ⊢
  simp only [decide_eq_false_iff_not] at hclean ⊢
  rintro ⟨other, hmem⟩
  apply hclean
  refine ⟨other, ?_⟩
  by_cases heq : other = coordinate
  · subst other
    simp [AdaptiveRevealProbe.State.addPending, hmem]
  · simpa [AdaptiveRevealProbe.State.addPending, Function.update_of_ne heq] using hmem

theorem tableHits_eq_false_of_install_eq_false
    (state : AdaptiveRevealProbe.State Coordinate) (table : Coordinate → Digest)
    (coordinate : Coordinate) (value : Digest)
    (hmiss : table coordinate ∉ state.pending coordinate)
    (hclean : AdaptiveRevealProbe.tableHits
      (state.install coordinate value) table = false) :
    AdaptiveRevealProbe.tableHits state table = false := by
  classical
  unfold AdaptiveRevealProbe.tableHits at hclean ⊢
  simp only [decide_eq_false_iff_not] at hclean ⊢
  rintro ⟨other, hmem⟩
  by_cases heq : other = coordinate
  · subst other
    exact hmiss hmem
  · apply hclean
    refine ⟨other, ?_⟩
    simpa [AdaptiveRevealProbe.State.install, Function.update_of_ne heq] using hmem

theorem tableHits_false_of_mem_runDetailed_done_false
    (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) alpha)
    (value : alpha)
    (hresult : .done false finalState value ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel computation)) :
    AdaptiveRevealProbe.tableHits state table = false := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      simp [AdaptiveRevealProbe.runDetailed] at hresult
      exact hresult.1
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [AdaptiveRevealProbe.runDetailed_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hrest
      | hashOutput =>
          rw [AdaptiveRevealProbe.runDetailed_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hrest
      | probe coordinate candidate =>
          rw [AdaptiveRevealProbe.runDetailed_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | some revealedValue =>
                  exact ih () state remaining (by simpa [hrevealed] using hresult)
              | none =>
                  apply tableHits_eq_false_of_addPending_eq_false state table coordinate candidate
                  exact ih () (state.addPending coordinate candidate) remaining
                    (by simpa [hrevealed] using hresult)
      | reveal coordinate =>
          rw [AdaptiveRevealProbe.runDetailed_reveal_query_bind] at hresult
          cases hrevealed : state.revealed coordinate with
          | some revealedValue =>
              exact ih revealedValue state fuel (by simpa [hrevealed] using hresult)
          | none =>
              by_cases hhit : table coordinate ∈ state.pending coordinate
              · simp [hrevealed, hhit] at hresult
              · apply tableHits_eq_false_of_install_eq_false state table coordinate
                  (table coordinate) hhit
                exact ih (table coordinate)
                  (state.install coordinate (table coordinate)) fuel
                  (by simpa [hrevealed, hhit] using hresult)

theorem mem_support_runDetailed_bind_probeFree
    (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (left : OracleComp (AdaptiveRevealProbe.World Coordinate) alpha)
    (next : alpha → OracleComp (AdaptiveRevealProbe.World Coordinate) beta)
    (hprobeFree : left.IsQueryBoundP AdaptiveRevealProbe.IsProbe 0)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (value : beta)
    (hresult : .done false finalState value ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel (left >>= next))) :
    ∃ leftState leftValue,
      .done false leftState leftValue ∈ support
          (AdaptiveRevealProbe.runDetailed table state fuel left) ∧
        .done false finalState value ∈ support
          (AdaptiveRevealProbe.runDetailed table leftState fuel (next leftValue)) := by
  rw [AdaptiveRevealProbe.runDetailed_bind_probeFree table state fuel left next hprobeFree,
    mem_support_bind_iff] at hresult
  obtain ⟨leftResult, hleft, hnext⟩ := hresult
  obtain ⟨leftState, leftValue, heq, hleftClean⟩ :=
    AdaptiveRevealProbe.runDetailed_probeFree_support table state fuel left hprobeFree hclean
      leftResult hleft
  subst leftResult
  exact ⟨leftState, leftValue, hleft, hnext⟩

theorem CoupledAt.mem_support_ordinary
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state finalState : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {masked : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {ordinary : StateT (QueryCache HashSpec) ProbComp alpha}
    {cache finalCache : SplitHashCache} {value : alpha}
    (hcoupled : CoupledAt parameter table state fuel masked ordinary cache)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache))) :
    (value, mergedCache parameter table finalCache) ∈
      support (ordinary.run (mergedCache parameter table cache)) := by
  have hprojected : some (value, mergedCache parameter table finalCache) ∈ support
      (projectDetailedCache parameter table <$>
        AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache)) := by
    rw [support_map]
    exact ⟨.done false finalState (value, finalCache), hresult, rfl⟩
  rw [hcoupled, support_map] at hprojected
  obtain ⟨ordinaryResult, hordinary, heq⟩ := hprojected
  exact Option.some.inj heq ▸ hordinary

theorem probingHashQuery_done_false_mem_ordinary
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (input : HashInput) (output : HashOutput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hresult : .done false finalState (output, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((probingHashQuery parameter input).run cache))) :
    (output, mergedCache parameter table finalCache) ∈ support
      ((randomOracle input).run (mergedCache parameter table cache)) := by
  cases hdecode : decodeProbe? parameter input with
  | none =>
      apply CoupledAt.mem_support_ordinary
        (parameter := parameter) (table := table) (state := state) (fuel := fuel)
        (masked := probingHashQuery parameter input) (ordinary := randomOracle input)
        (cache := cache) (finalState := finalState) (finalCache := finalCache)
        (value := output)
      · exact runDetailed_probingHashQuery_decode_none parameter table state fuel cache input
          hdecode hclean
      · exact hresult
  | some probe =>
      cases fuel with
      | zero =>
          rw [probingHashQuery_run_eq, hdecode] at hresult
          change .done false finalState (output, finalCache) ∈ support
            (AdaptiveRevealProbe.runDetailed table state 0
              ((liftM (OracleSpec.query
                (spec := AdaptiveRevealProbe.World Coordinate)
                (.probe (probe.index, probe.tree, probe.leafIdx) probe.candidate)) :
                  OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
                (splitHashQuery (.ordinary input)).run cache)) at hresult
          rw [AdaptiveRevealProbe.runDetailed_probe_query_bind] at hresult
          simp at hresult
      | succ remaining =>
          cases hrevealed : state.revealed
              (probe.index, probe.tree, probe.leafIdx) with
          | none =>
              by_cases hhit : table (probe.index, probe.tree, probe.leafIdx) = probe.candidate
              · have := runDetailed_probingHashQuery_hidden_hit parameter table state remaining
                  cache input probe hdecode hrevealed hhit
                  (.done false finalState (output, finalCache)) hresult
                change false = true at this
                simp at this
              · apply CoupledAt.mem_support_ordinary
                  (parameter := parameter) (table := table) (state := state)
                  (fuel := remaining + 1) (masked := probingHashQuery parameter input)
                  (ordinary := randomOracle input) (cache := cache)
                  (finalState := finalState) (finalCache := finalCache) (value := output)
                · exact runDetailed_probingHashQuery_hidden_miss parameter table state remaining
                    cache input probe hdecode hrevealed hclean hhit
                · exact hresult
          | some value =>
              by_cases hhit : table (probe.index, probe.tree, probe.leafIdx) = probe.candidate
              · apply CoupledAt.mem_support_ordinary
                  (parameter := parameter) (table := table) (state := state)
                  (fuel := remaining + 1) (masked := probingHashQuery parameter input)
                  (ordinary := randomOracle input) (cache := cache)
                  (finalState := finalState) (finalCache := finalCache) (value := output)
                · exact runDetailed_probingHashQuery_revealed_hit parameter table state remaining
                    cache input probe hdecode value hrevealed hclean hhit hsynced
                · exact hresult
              · apply CoupledAt.mem_support_ordinary
                  (parameter := parameter) (table := table) (state := state)
                  (fuel := remaining + 1) (masked := probingHashQuery parameter input)
                  (ordinary := randomOracle input) (cache := cache)
                  (finalState := finalState) (finalCache := finalCache) (value := output)
                · exact runDetailed_probingHashQuery_revealed_miss parameter table state remaining
                    cache input probe hdecode value hrevealed hclean hhit
                · exact hresult

theorem probingHashQuery_done_false_invariants
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (input : HashInput) (output : HashOutput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hresult : .done false finalState (output, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((probingHashQuery parameter input).run cache))) :
    AdaptiveRevealProbe.tableHits finalState table = false ∧
      finalState.revealed = state.revealed := by
  cases hdecode : decodeProbe? parameter input with
  | none =>
      rw [probingHashQuery_run_eq, hdecode] at hresult
      obtain ⟨value, heq⟩ := AdaptiveRevealProbe.runDetailed_stateFree_support table state fuel
        ((splitHashQuery (.ordinary input)).run cache)
        (splitHashQuery_stateFree (.ordinary input) cache) hclean
        (.done false finalState (output, finalCache)) hresult
      have hstate := (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1
      exact ⟨hstate ▸ hclean, hstate ▸ rfl⟩
  | some probe =>
      cases fuel with
      | zero =>
          rw [probingHashQuery_run_eq, hdecode] at hresult
          change .done false finalState (output, finalCache) ∈ support
            (AdaptiveRevealProbe.runDetailed table state 0
              ((liftM (OracleSpec.query
                (spec := AdaptiveRevealProbe.World Coordinate)
                (.probe (probe.index, probe.tree, probe.leafIdx) probe.candidate)) :
                  OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
                (splitHashQuery (.ordinary input)).run cache)) at hresult
          rw [AdaptiveRevealProbe.runDetailed_probe_query_bind] at hresult
          simp at hresult
      | succ remaining =>
          have hresultOriginal := hresult
          rw [probingHashQuery_run_eq, hdecode] at hresult
          change .done false finalState (output, finalCache) ∈ support
            (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
              ((liftM (OracleSpec.query
                (spec := AdaptiveRevealProbe.World Coordinate)
                (.probe (probe.index, probe.tree, probe.leafIdx) probe.candidate)) :
                  OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
                (splitHashQuery (.ordinary input)).run cache)) at hresult
          rw [AdaptiveRevealProbe.runDetailed_probe_query_bind] at hresult
          cases hrevealed : state.revealed
              (probe.index, probe.tree, probe.leafIdx) with
          | none =>
              simp only [hrevealed] at hresult
              by_cases hhit : table (probe.index, probe.tree, probe.leafIdx) = probe.candidate
              · have hhitEq := runDetailed_probingHashQuery_hidden_hit parameter table state
                  remaining cache input probe hdecode hrevealed hhit
                  (.done false finalState (output, finalCache)) hresultOriginal
                change false = true at hhitEq
                simp at hhitEq
              · have hnextClean := AdaptiveRevealProbe.tableHits_addPending_eq_false state table
                  (probe.index, probe.tree, probe.leafIdx) probe.candidate hclean hhit
                obtain ⟨value, heq⟩ :=
                  AdaptiveRevealProbe.runDetailed_stateFree_support table
                    (state.addPending (probe.index, probe.tree, probe.leafIdx) probe.candidate)
                    remaining ((splitHashQuery (.ordinary input)).run cache)
                    (splitHashQuery_stateFree (.ordinary input) cache) hnextClean
                    (.done false finalState (output, finalCache)) hresult
                have hstate := (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1
                refine ⟨hstate ▸ hnextClean, ?_⟩
                rw [hstate]
                rfl
          | some value =>
              simp only [hrevealed] at hresult
              obtain ⟨resultValue, heq⟩ :=
                AdaptiveRevealProbe.runDetailed_stateFree_support table state remaining
                  ((splitHashQuery (.ordinary input)).run cache)
                  (splitHashQuery_stateFree (.ordinary input) cache) hclean
                  (.done false finalState (output, finalCache)) hresult
              have hstate := (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1
              exact ⟨hstate ▸ hclean, hstate ▸ rfl⟩

theorem probingHashQuery_done_false_clean
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (input : HashInput) (output : HashOutput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hresult : .done false finalState (output, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((probingHashQuery parameter input).run cache))) :
    AdaptiveRevealProbe.tableHits finalState table = false :=
  (probingHashQuery_done_false_invariants parameter table state finalState fuel cache finalCache
    input output hclean hresult).1

theorem probingHashQuery_cachePreserving
    (parameter : PublicParameter) (input : HashInput) :
    CachePreserving (probingHashQuery parameter input) := by
  intro initial result hresult
  rw [probingHashQuery_run_eq] at hresult
  cases hdecode : decodeProbe? parameter input with
  | none =>
      simp only [hdecode] at hresult
      exact splitHashQuery_cachePreserving (.ordinary input) initial result hresult
  | some probe =>
      simp only [hdecode, mem_support_bind_iff] at hresult
      obtain ⟨probeResult, _hprobe, hresult⟩ := hresult
      exact splitHashQuery_cachePreserving (.ordinary input) initial result hresult

theorem probingHashQuery_done_false_revealedSynced
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (input : HashInput) (output : HashOutput)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hresult : .done false finalState (output, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((probingHashQuery parameter input).run cache))) :
    RevealedSynced parameter table finalState finalCache := by
  have hrevealed := (probingHashQuery_done_false_invariants parameter table state finalState
    fuel cache finalCache input output hclean hresult).2
  have hraw : (output, finalCache) ∈ support ((probingHashQuery parameter input).run cache) :=
    AdaptiveRevealProbe.mem_support_of_mem_runDetailed_done table state finalState fuel
      ((probingHashQuery parameter input).run cache) false (output, finalCache) hresult
  have hcacheLe : SplitCacheLE cache finalCache :=
    probingHashQuery_cachePreserving parameter input cache (output, finalCache) hraw
  intro coordinate value hfinalRevealed
  have hinitialRevealed : state.revealed coordinate = some value := by
    rw [← hrevealed]
    exact hfinalRevealed
  obtain ⟨hvalue, hiddenOutput, hhidden, hordinary⟩ :=
    hsynced coordinate value hinitialRevealed
  exact ⟨hvalue, hiddenOutput, hcacheLe _ _ hhidden, hcacheLe _ _ hordinary⟩

set_option maxRecDepth 2000 in
theorem revealedSynced_of_mem_runDetailed_revealSequence {n : Nat}
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
    RevealedSynced parameter table finalState finalCache := by
  induction n generalizing state cache finalState finalCache with
  | zero =>
      simp only [sequenceFin, StateT.run_pure] at hresult
      simp [AdaptiveRevealProbe.runDetailed, hclean] at hresult
      obtain ⟨hstate, hvalues, hcache⟩ := hresult
      subst finalState
      subst finalCache
      exact hsynced
  | succ n ih =>
      rw [sequenceFin, StateT.run_bind] at hresult
      obtain ⟨headState, headResult, hhead, hafterHead⟩ :=
        mem_support_runDetailed_bind_probeFree table state finalState fuel
          ((revealFtsSecret parameter (coordinates 0)).run cache) _
          (revealFtsSecret_probeFree parameter (coordinates 0) cache) hclean
          (values, finalCache) hresult
      rcases headResult with ⟨head, headCache⟩
      have hcoordinateZero : coordinates 0 =
          (index, (coordinates 0).2.1, (coordinates 0).2.2) := by
        rcases hcoordinate : coordinates 0 with ⟨coordinateIndex, tree, leafIdx⟩
        have hindex := hcoordinates 0
        rw [hcoordinate] at hindex
        simpa using hindex
      have hhiddenZero : ∃ output,
          cache (.hiddenLeaf (coordinates 0)) = some output := by
        rw [hcoordinateZero]
        exact hcached (coordinates 0).2.1 (coordinates 0).2.2
      have hheadClean : AdaptiveRevealProbe.tableHits headState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table state headState fuel
          ((revealFtsSecret parameter (coordinates 0)).run cache)
          (revealFtsSecret_probeFree parameter (coordinates 0) cache) hclean
          (head, headCache) hhead
      have hheadSynced : RevealedSynced parameter table headState headCache :=
        revealedSynced_of_mem_runDetailed_revealFtsSecret parameter table state headState fuel
          cache headCache (coordinates 0) head hclean hsynced hhiddenZero hhead
      have hheadCached : HiddenIndexCached index headCache :=
        hiddenIndexCached_of_mem_runDetailed_revealFtsSecret parameter table index state
          headState fuel cache headCache (coordinates 0) head hclean hsynced hcached
          (hcoordinates 0) hhead
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
      have htailSynced : RevealedSynced parameter table tailState tailCache :=
        ih (fun position => coordinates position.succ)
          (fun position => hcoordinates position.succ)
          (state := headState) (cache := headCache)
          (finalState := tailState) (finalCache := tailCache)
          hheadClean hheadSynced hheadCached tail htail
      have hparts := AdaptiveRevealProbe.DetailedResult.done.inj hfinish
      have hfinalState := hparts.2.1
      have hfinalCache := congrArg Prod.snd hparts.2.2
      subst finalState
      change finalCache = tailCache at hfinalCache
      rw [hfinalCache]
      exact htailSynced

theorem revealedSynced_of_mem_runDetailed_revealSelectedFtsSecrets
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
    RevealedSynced parameter table finalState finalCache := by
  unfold revealSelectedFtsSecrets at hresult
  exact revealedSynced_of_mem_runDetailed_revealSequence parameter table index
    (fun tree => (index, tree, leaves (ftsIndexOf tree))) (fun tree => rfl)
    state finalState fuel cache finalCache hclean hsynced hcached values hresult

set_option maxRecDepth 4000 in
theorem revealedSynced_of_mem_runDetailed_maskedSignAfterDigest
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
    RevealedSynced secretKey.parameter table finalState finalCache := by
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
  have hlayersCached : HiddenIndexCached index layersCache :=
    hiddenIndexCached_of_mem_runDetailed_maskedSignLayers secretKey table pathState
      layersState fuel pathCache layersCache index layers hpathClean hlayers
  cases hparts : traverseOption layers with
  | none =>
      simp only [hparts] at hafterLayers
      simp [AdaptiveRevealProbe.runDetailed, hlayersClean] at hafterLayers
      obtain ⟨hstate, hsignature, hvalueCache⟩ := hafterLayers
      subst finalState
      cases hvalueCache
      exact hlayersSynced
  | some parts =>
      simp only [hparts, StateT.run_bind] at hafterLayers
      obtain ⟨selectedState, selectedResult, hselected, hfinish⟩ :=
        mem_support_runDetailed_bind_probeFree table layersState finalState fuel
          ((revealSelectedFtsSecrets secretKey.parameter index leaves).run layersCache) _
          (revealSelectedFtsSecrets_probeFree secretKey.parameter index leaves layersCache)
          hlayersClean (signature, finalCache) hafterLayers
      rcases selectedResult with ⟨selected, selectedCache⟩
      have hselectedSynced :
          RevealedSynced secretKey.parameter table selectedState selectedCache :=
        revealedSynced_of_mem_runDetailed_revealSelectedFtsSecrets secretKey.parameter table
          index leaves layersState selectedState fuel layersCache selectedCache hlayersClean
          hlayersSynced hlayersCached selected hselected
      have hselectedClean : AdaptiveRevealProbe.tableHits selectedState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table layersState selectedState fuel
          ((revealSelectedFtsSecrets secretKey.parameter index leaves).run layersCache)
          (revealSelectedFtsSecrets_probeFree secretKey.parameter index leaves layersCache)
          hlayersClean (selected, selectedCache) hselected
      simp [AdaptiveRevealProbe.runDetailed, hselectedClean] at hfinish
      obtain ⟨hstate, hsignature, hvalueCache⟩ := hfinish
      subst finalState
      cases hvalueCache
      exact hselectedSynced

set_option maxRecDepth 10000 in
theorem revealedSynced_of_mem_runDetailed_maskedSignWithView
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (message : Message)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (result : Option Signature × Option FewTimeView)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((maskedSignWithView secretKey message).run cache))) :
    RevealedSynced secretKey.parameter table finalState finalCache := by
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
  cases selected with
  | none =>
      simp [AdaptiveRevealProbe.runDetailed, hloopClean] at hafterLoop
      obtain ⟨hstate, hvalue, hcache⟩ := hafterLoop
      subst finalState
      subst finalCache
      exact hloopSynced
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
      have hsignatureClean : AdaptiveRevealProbe.tableHits signatureState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table loopState signatureState fuel
          ((maskedSignAfterDigest secretKey randomness index leaves).run loopCache)
          (maskedSignAfterDigest_probeFree secretKey randomness index leaves loopCache)
          hloopClean (signature, signatureCache) hsignature
      simp [AdaptiveRevealProbe.runDetailed, hsignatureClean] at hfinish
      obtain ⟨hstate, hvalue, hcache⟩ := hfinish
      subst finalState
      subst finalCache
      exact hsignatureSynced

theorem revealedSynced_of_mem_runDetailed_maskedSigningImpl
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (message : Message)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (signature : Option Signature)
    (hresult : .done false finalState (signature, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((maskedSigningImpl secretKey message).run cache))) :
    RevealedSynced secretKey.parameter table finalState finalCache := by
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
  exact revealedSynced_of_mem_runDetailed_maskedSignWithView secretKey table state viewState
    fuel cache viewValue.2 message hclean hsynced viewValue.1 hviewResult

set_option maxRecDepth 10000 in
theorem maskedExpandedAdversaryImpl_done_false
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache)
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (hresult : .done false finalState (output, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((maskedExpandedAdversaryImpl secretKey.parameter secretKey input).run cache))) :
    (output, mergedCache secretKey.parameter table finalCache) ∈ support
        ((unloggedMappedAdversaryImpl
          (secretKeyWithFtsTable secretKey table) input).run
            (mergedCache secretKey.parameter table cache)) ∧
      AdaptiveRevealProbe.tableHits finalState table = false ∧
      RevealedSynced secretKey.parameter table finalState finalCache := by
  revert output
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl n =>
          intro output hresult
          change unifSpec.Range n at output
          change .done false finalState (output, finalCache) ∈ support
            (AdaptiveRevealProbe.runDetailed table state fuel
              ((splitUniformImpl n).run cache)) at hresult
          change (output, mergedCache secretKey.parameter table finalCache) ∈ support
              ((unifFwdImpl HashSpec n).run
                (mergedCache secretKey.parameter table cache)) ∧
            AdaptiveRevealProbe.tableHits finalState table = false ∧
            RevealedSynced secretKey.parameter table finalState finalCache
          have hactual := CoupledAt.mem_support_ordinary
            (parameter := secretKey.parameter) (table := table) (state := state)
            (fuel := fuel) (masked := splitUniformImpl n) (ordinary := unifFwdImpl HashSpec n)
            (cache := cache) (finalState := finalState) (finalCache := finalCache)
            (value := output)
            ((coupled_splitUniformImpl secretKey.parameter table state fuel n hclean).coupledAt
              cache) hresult
          have hmasked : .done false finalState (output, finalCache) ∈ support
              (AdaptiveRevealProbe.runDetailed table state fuel
                ((splitUniformImpl n).run cache)) := hresult
          have hfinalClean := tableHits_false_of_mem_runDetailed_probeFree table state finalState
            fuel ((splitUniformImpl n).run cache) (splitUniformImpl_probeFree n cache) hclean
            (output, finalCache) hmasked
          have hfinalSynced := revealedSynced_of_mem_runDetailed_stateFree
            secretKey.parameter table state finalState fuel cache finalCache output
            (splitUniformImpl n) hclean hsynced (splitUniformImpl_stateFree n)
            (splitUniformImpl_cachePreserving n) hmasked
          refine ⟨?_, hfinalClean, hfinalSynced⟩
          exact hactual
      | inr hashInput =>
          intro output hresult
          change HashOutput at output
          change .done false finalState (output, finalCache) ∈ support
            (AdaptiveRevealProbe.runDetailed table state fuel
              ((probingHashQuery secretKey.parameter hashInput).run cache)) at hresult
          have hmasked : .done false finalState (output, finalCache) ∈ support
              (AdaptiveRevealProbe.runDetailed table state fuel
                ((probingHashQuery secretKey.parameter hashInput).run cache)) := hresult
          refine ⟨?_, probingHashQuery_done_false_clean secretKey.parameter table state
            finalState fuel cache finalCache hashInput output hclean hmasked, ?_⟩
          · change (output, mergedCache secretKey.parameter table finalCache) ∈ support
              ((randomOracle hashInput).run
                (mergedCache secretKey.parameter table cache))
            exact probingHashQuery_done_false_mem_ordinary secretKey.parameter table state
              finalState fuel cache finalCache hashInput output hclean hsynced hmasked
          · exact probingHashQuery_done_false_revealedSynced secretKey.parameter table state
              finalState fuel cache finalCache hashInput output hclean hsynced hmasked
  | inr message =>
      intro output hresult
      change SigningSpec.Range message at output
      change .done false finalState (output, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state fuel
          ((maskedSigningImpl secretKey message).run cache)) at hresult
      change (output, mergedCache secretKey.parameter table finalCache) ∈ support
            ((simulateQ romImpl
              (scheme.sign (secretKeyWithFtsTable secretKey table) message)).run
                (mergedCache secretKey.parameter table cache)) ∧
          AdaptiveRevealProbe.tableHits finalState table = false ∧
          RevealedSynced secretKey.parameter table finalState finalCache
      have hmasked : .done false finalState (output, finalCache) ∈ support
          (AdaptiveRevealProbe.runDetailed table state fuel
            ((maskedSigningImpl secretKey message).run cache)) := hresult
      have hactual := CoupledAt.mem_support_ordinary
        (parameter := secretKey.parameter) (table := table) (state := state) (fuel := fuel)
        (masked := maskedSigningImpl secretKey message)
        (ordinary := simulateQ romImpl
          (scheme.sign (secretKeyWithFtsTable secretKey table) message))
        (cache := cache) (finalState := finalState) (finalCache := finalCache)
        (value := output)
        (coupledAt_maskedSigningImpl secretKey table state fuel cache message hclean hsynced)
        hmasked
      have hfinalClean := tableHits_false_of_mem_runDetailed_probeFree table state finalState
        fuel ((maskedSigningImpl secretKey message).run cache)
        (by
          have hprobeFree : ProbeFree (maskedSigningImpl secretKey message) := by
            unfold maskedSigningImpl
            exact (maskedSignWithView_probeFree secretKey message).map Prod.fst
          exact hprobeFree cache)
        hclean (output, finalCache) hmasked
      refine ⟨?_, hfinalClean, ?_⟩
      · exact hactual
      · exact revealedSynced_of_mem_runDetailed_maskedSigningImpl secretKey table state
          finalState fuel cache finalCache message hclean hsynced output hmasked

set_option maxRecDepth 10000 in
theorem simulateQ_maskedExpandedAdversaryImpl_done_false
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (value : alpha)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          computation).run cache))) :
    (value, mergedCache secretKey.parameter table finalCache) ∈ support
        ((simulateQ
          (unloggedMappedAdversaryImpl (secretKeyWithFtsTable secretKey table))
          computation).run (mergedCache secretKey.parameter table cache)) ∧
      AdaptiveRevealProbe.tableHits finalState table = false ∧
      RevealedSynced secretKey.parameter table finalState finalCache := by
  induction computation using OracleComp.inductionOn generalizing
      state fuel cache finalState finalCache with
  | pure result =>
      simp [simulateQ_pure, AdaptiveRevealProbe.runDetailed, hclean] at hresult
      obtain ⟨hstate, hvalue, hcache⟩ := hresult
      subst finalState
      subst value
      subst finalCache
      exact ⟨by simp [simulateQ_pure], hclean, hsynced⟩
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hresult
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
                      (next result.1)).run result.2)
                  (splitUniformImpl_probeFree n cache) hclean
                  (value, finalCache) (by
                    simpa [maskedExpandedAdversaryImpl, probingRomImpl,
                      probingHashImpl] using hresult)
              rcases queryResult with ⟨output, queryCache⟩
              have hstep := maskedExpandedAdversaryImpl_done_false secretKey table state
                queryState fuel cache queryCache (.inl (.inl n)) output hclean hsynced hquery
              have htail := ih output queryState finalState fuel queryCache finalCache
                hstep.2.1 hstep.2.2 hrest
              refine ⟨?_, htail.2.1, htail.2.2⟩
              rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
              exact ⟨(output, mergedCache secretKey.parameter table queryCache), hstep.1,
                htail.1⟩
          | inr hashInput =>
              have hhashResult : .done false finalState (value, finalCache) ∈ support
                  (AdaptiveRevealProbe.runDetailed table state fuel
                    ((probingHashQuery secretKey.parameter hashInput).run cache >>= fun result =>
                      (simulateQ
                        (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                        (next result.1)).run result.2)) := by
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
                          (next result.1)).run result.2)
                      (hhashProbeFree cache) hclean (value, finalCache) hhashResult
                  rcases queryResult with ⟨output, queryCache⟩
                  have hstep := maskedExpandedAdversaryImpl_done_false secretKey table state
                    queryState fuel cache queryCache (.inl (.inr hashInput)) output hclean
                    hsynced hquery
                  have htail := ih output queryState finalState fuel queryCache finalCache
                    hstep.2.1 hstep.2.2 hrest
                  refine ⟨?_, htail.2.1, htail.2.2⟩
                  rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
                  exact ⟨(output, mergedCache secretKey.parameter table queryCache), hstep.1,
                    htail.1⟩
              | some probe =>
                  rw [probingHashQuery_run_eq, hdecode] at hhashResult
                  change .done false finalState (value, finalCache) ∈ support
                    (AdaptiveRevealProbe.runDetailed table state fuel
                      ((liftM (OracleSpec.query
                        (spec := AdaptiveRevealProbe.World Coordinate)
                        (.probe (probe.index, probe.tree, probe.leafIdx) probe.candidate)) :
                          OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
                        (splitHashQuery (.ordinary hashInput)).run cache >>= fun result =>
                          (simulateQ
                            (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                            (next result.1)).run result.2)) at hhashResult
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
                                    (next result.1)).run result.2)
                                (value, finalCache) hhashResult
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
                                    (next result.1)).run result.2)
                                (splitHashQuery_probeFree (.ordinary hashInput) cache)
                                hpostClean (value, finalCache) hhashResult
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
                            have htail := ih output queryState finalState remaining queryCache
                              finalCache hstep.2.1 hstep.2.2 hrest
                            refine ⟨?_, htail.2.1, htail.2.2⟩
                            rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
                            exact ⟨(output, mergedCache secretKey.parameter table queryCache),
                              hstep.1, htail.1⟩
                      | some revealedValue =>
                          simp only [hrevealed] at hhashResult
                          obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
                            mem_support_runDetailed_bind_probeFree table state finalState
                              remaining ((splitHashQuery (.ordinary hashInput)).run cache)
                              (fun result =>
                                (simulateQ
                                  (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                                  (next result.1)).run result.2)
                              (splitHashQuery_probeFree (.ordinary hashInput) cache)
                              hclean (value, finalCache) hhashResult
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
                          have htail := ih output queryState finalState remaining queryCache
                            finalCache hstep.2.1 hstep.2.2 hrest
                          refine ⟨?_, htail.2.1, htail.2.2⟩
                          rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
                          exact ⟨(output, mergedCache secretKey.parameter table queryCache),
                            hstep.1, htail.1⟩
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
                  (next result.1)).run result.2)
              (hsignProbeFree cache)
              hclean (value, finalCache) (by
                simpa [maskedExpandedAdversaryImpl, probingRomImpl,
                  probingHashImpl] using hresult)
          rcases queryResult with ⟨output, queryCache⟩
          have hstep := maskedExpandedAdversaryImpl_done_false secretKey table state
            queryState fuel cache queryCache (.inr message) output hclean hsynced hquery
          have htail := ih output queryState finalState fuel queryCache finalCache
            hstep.2.1 hstep.2.2 hrest
          refine ⟨?_, htail.2.1, htail.2.2⟩
          rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
          exact ⟨(output, mergedCache secretKey.parameter table queryCache), hstep.1,
            htail.1⟩

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
  | pure value =>
      simp [signingTraceComputation]
  | query_bind input next ih =>
      simp [signingTraceComputation, ih]

set_option maxRecDepth 10000 in
theorem simulateQ_maskedExpandedAdversaryImpl_withTrace_done_false
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (value : alpha) (log : QueryLog SigningSpec)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (hresult : .done false finalState ((value, log), finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((simulateQ (QueryImpl.withTraceAppend
          (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          signingLogFragment) computation).run.run cache))) :
    ((value, log), mergedCache secretKey.parameter table finalCache) ∈ support
        ((simulateQ (QueryImpl.withTraceAppend
          (unloggedMappedAdversaryImpl (secretKeyWithFtsTable secretKey table))
          signingLogFragment) computation).run.run
            (mergedCache secretKey.parameter table cache)) ∧
      AdaptiveRevealProbe.tableHits finalState table = false ∧
      RevealedSynced secretKey.parameter table finalState finalCache := by
  rw [simulateQ_withTraceAppend_run_eq_signingTraceComputation] at hresult ⊢
  exact simulateQ_maskedExpandedAdversaryImpl_done_false secretKey table
    (signingTraceComputation computation) state finalState fuel cache finalCache
    (value, log) hclean hsynced hresult

set_option maxRecDepth 10000 in
theorem simulateQ_probingRomImpl_done_false
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp OracleWorld alpha)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (value : alpha)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((simulateQ (probingRomImpl secretKey.parameter) computation).run cache))) :
    (value, mergedCache secretKey.parameter table finalCache) ∈ support
        ((simulateQ romImpl computation).run
          (mergedCache secretKey.parameter table cache)) ∧
      AdaptiveRevealProbe.tableHits finalState table = false ∧
      RevealedSynced secretKey.parameter table finalState finalCache := by
  letI directLift : MonadLift (OracleQuery OracleWorld)
      (OracleQuery (OracleWorld + SigningSpec)) :=
    (OracleQuery.subSpec_add_left
      (spec₁ := OracleWorld) (spec₂ := SigningSpec)).toMonadLift
  let lifted : OracleComp (OracleWorld + SigningSpec) alpha := liftM computation
  have hmasked : simulateQ
      (maskedExpandedAdversaryImpl secretKey.parameter secretKey) lifted =
        simulateQ (probingRomImpl secretKey.parameter) computation := by
    change simulateQ
      (probingRomImpl secretKey.parameter + maskedSigningImpl secretKey)
        (liftM computation) = _
    simpa [lifted] using
      (QueryImpl.simulateQ_add_liftM_left
        (probingRomImpl secretKey.parameter) (maskedSigningImpl secretKey) computation)
  let signingHandler : QueryImpl SigningSpec
      (StateT (QueryCache HashSpec) ProbComp) :=
    fun message => simulateQ romImpl
      (scheme.sign (secretKeyWithFtsTable secretKey table) message)
  have hactualHandler :
      unloggedMappedAdversaryImpl (secretKeyWithFtsTable secretKey table) =
        romImpl + signingHandler := by
    funext input
    cases input <;> rfl
  have hactual : simulateQ
      (unloggedMappedAdversaryImpl (secretKeyWithFtsTable secretKey table)) lifted =
        simulateQ romImpl computation := by
    rw [hactualHandler]
    simpa [lifted] using
      (QueryImpl.simulateQ_add_liftM_left romImpl signingHandler computation)
  rw [← hmasked] at hresult
  rw [← hactual]
  exact simulateQ_maskedExpandedAdversaryImpl_done_false secretKey table lifted
    state finalState fuel cache finalCache value hclean hsynced hresult

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

noncomputable def tracedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) Bool := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure (decide (SigningTranscript.Valid log ∧
    ¬SigningTranscript.Contains log forgery) && verified)

theorem simulateQ_maskedExpanded_tracedGameRestComputation
    (adversary : Adversary) (secretKey : SecretKey) :
    simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
        (tracedGameRestComputation adversary ⟨secretKey.root, secretKey.parameter⟩) = (do
      let (forgery, log) ←
        (simulateQ (QueryImpl.withTraceAppend
          (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          signingLogFragment)
          (adversary.main ⟨secretKey.root, secretKey.parameter⟩)).run
      let verified ← simulateQ (probingRomImpl secretKey.parameter)
        (scheme.verify ⟨secretKey.root, secretKey.parameter⟩
          forgery.message forgery.signature)
      pure (decide (SigningTranscript.Valid log ∧
        ¬SigningTranscript.Contains log forgery) && verified)) := by
  unfold tracedGameRestComputation
  rw [simulateQ_bind,
    ← simulateQ_withTraceAppend_run_eq_signingTraceComputation]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind]
  change (do
    let verified ← simulateQ
      (probingRomImpl secretKey.parameter + maskedSigningImpl secretKey)
      (liftOracleWorldLeft
        (scheme.verify ⟨secretKey.root, secretKey.parameter⟩
          forgery.message forgery.signature))
    pure (decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log forgery) && verified)) = _
  rw [simulateQ_liftOracleWorldLeft]

theorem writerTMapBase_expanded_withTraceAppend_eq_unlogged
    (secretKey : SecretKey) :
    QueryImpl.writerTMapBase romImpl
        (QueryImpl.withTraceAppend (expandedAdversaryImpl secretKey)
          signingLogFragment) =
      QueryImpl.withTraceAppend (unloggedMappedAdversaryImpl secretKey)
        signingLogFragment := by
  funext input
  apply WriterT.ext
  simp [QueryImpl.writerTMapBase,
    unloggedMappedAdversaryImpl_eq_simulateQ_expanded]

theorem simulateQ_unloggedMapped_liftOracleWorldLeft
    (secretKey : SecretKey) (computation : OracleComp OracleWorld alpha) :
    simulateQ (unloggedMappedAdversaryImpl secretKey)
        (liftOracleWorldLeft computation) =
      simulateQ romImpl computation := by
  let signingHandler : QueryImpl SigningSpec
      (StateT (QueryCache HashSpec) ProbComp) :=
    fun message => simulateQ romImpl (scheme.sign secretKey message)
  have hhandler : unloggedMappedAdversaryImpl secretKey =
      romImpl + signingHandler := by
    funext input
    cases input <;> rfl
  rw [hhandler, simulateQ_liftOracleWorldLeft]

theorem simulateQ_unloggedMapped_tracedGameRestComputation
    (adversary : Adversary) (secretKey : SecretKey) :
    simulateQ (unloggedMappedAdversaryImpl secretKey)
        (tracedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩) =
      simulateQ romImpl
        (gameRest scheme adversary ⟨secretKey.root, secretKey.parameter⟩ secretKey) := by
  have hadversary :
      simulateQ romImpl
          ((simulateQ (forwardOracles + signingOracle scheme secretKey)
            (adversary.main ⟨secretKey.root, secretKey.parameter⟩)).run) =
        (simulateQ (QueryImpl.withTraceAppend
          (unloggedMappedAdversaryImpl secretKey) signingLogFragment)
          (adversary.main ⟨secretKey.root, secretKey.parameter⟩)).run := by
    rw [forwardOracles_add_signingOracle_eq_withTraceAppend,
      QueryImpl.simulateQ_writerTMapBase_run,
      writerTMapBase_expanded_withTraceAppend_eq_unlogged]
  unfold tracedGameRestComputation gameRest
  rw [simulateQ_bind,
    ← simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    simulateQ_bind, hadversary]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind, simulateQ_bind,
    simulateQ_unloggedMapped_liftOracleWorldLeft]
  rfl

theorem maskedGameAfterSecrets_eq_tracedGameRestComputation
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    maskedGameAfterSecrets adversary parameter otsSecret = (do
      let root ← simulateQ ordinaryHashImpl
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
      let secretKey : SecretKey :=
        ⟨parameter, root, otsSecret, fun _index _tree _leafIdx => 0⟩
      simulateQ (maskedExpandedAdversaryImpl parameter secretKey)
        (tracedGameRestComputation adversary ⟨root, parameter⟩)) := by
  unfold maskedGameAfterSecrets
  apply bind_congr
  intro root
  exact (simulateQ_maskedExpanded_tracedGameRestComputation adversary
    ⟨parameter, root, otsSecret, fun _index _tree _leafIdx => 0⟩).symm

theorem simulateQ_romImpl_gameAfterSecrets_eq_tracedGameRestComputation
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) = (do
      let root ← simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
      let secretKey : SecretKey :=
        ⟨parameter, root, otsSecret, ftsSecret⟩
      simulateQ (unloggedMappedAdversaryImpl secretKey)
        (tracedGameRestComputation adversary ⟨root, parameter⟩)) := by
  unfold gameAfterSecrets
  rw [simulateQ_bind]
  have hroot : simulateQ romImpl
      (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
        OracleComp HashSpec Digest)) =
        simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
      (liftM (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
        OracleComp HashSpec Digest)) = _
    exact QueryImpl.simulateQ_add_liftM_right _ _ _
  rw [hroot]
  apply bind_congr
  intro root
  exact (simulateQ_unloggedMapped_tracedGameRestComputation adversary
    ⟨parameter, root, otsSecret, ftsSecret⟩).symm

set_option maxRecDepth 20000 in
theorem maskedGameAfterSecrets_done_false_mem_gameAfterSecrets
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest)
    (finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (finalCache : SplitHashCache) (value : Bool)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty fuel
        ((maskedGameAfterSecrets adversary parameter otsSecret).run
          emptySplitHashCache))) :
    (value, mergedCache parameter table finalCache) ∈ support
        ((simulateQ romImpl
          (gameAfterSecrets adversary parameter otsSecret
            (fun index tree leafIdx => table (index, tree, leafIdx)))).run ∅) ∧
      AdaptiveRevealProbe.tableHits finalState table = false ∧
      RevealedSynced parameter table finalState finalCache := by
  let rootComputation : OracleComp HashSpec Digest :=
    treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)
  have hinitialClean : AdaptiveRevealProbe.tableHits
      (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = false := by
    simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]
  rw [maskedGameAfterSecrets_eq_tracedGameRestComputation,
    StateT.run_bind] at hresult
  obtain ⟨rootState, rootResult, hroot, hrest⟩ :=
    mem_support_runDetailed_bind_probeFree table AdaptiveRevealProbe.State.empty
      finalState fuel
      ((simulateQ ordinaryHashImpl rootComputation).run emptySplitHashCache)
      (fun result =>
        let secretKey : SecretKey :=
          ⟨parameter, result.1, otsSecret, fun _index _tree _leafIdx => 0⟩
        (simulateQ (maskedExpandedAdversaryImpl parameter secretKey)
          (tracedGameRestComputation adversary ⟨result.1, parameter⟩)).run result.2)
      (simulateQ_ordinaryHashImpl_probeFree rootComputation emptySplitHashCache)
      hinitialClean (value, finalCache) (by simpa [rootComputation] using hresult)
  rcases rootResult with ⟨root, rootCache⟩
  let maskedSecretKey : SecretKey :=
    ⟨parameter, root, otsSecret, fun _index _tree _leafIdx => 0⟩
  have hrootActual := CoupledAt.mem_support_ordinary
    (parameter := parameter) (table := table)
    (state := AdaptiveRevealProbe.State.empty) (fuel := fuel)
    (masked := simulateQ ordinaryHashImpl rootComputation)
    (ordinary := simulateQ (randomOracle : QueryImpl HashSpec _) rootComputation)
    (cache := emptySplitHashCache) (finalState := rootState)
    (finalCache := rootCache) (value := root)
    ((coupled_simulateQ_ordinaryHashImpl parameter table
      AdaptiveRevealProbe.State.empty fuel rootComputation hinitialClean
      (ordinaryOnly_treeRoot parameter table topLayer rootTree
        (otsSecret topLayer rootTree))).coupledAt emptySplitHashCache) hroot
  have hrootClean := tableHits_false_of_mem_runDetailed_probeFree table
    AdaptiveRevealProbe.State.empty rootState fuel
    ((simulateQ ordinaryHashImpl rootComputation).run emptySplitHashCache)
    (simulateQ_ordinaryHashImpl_probeFree rootComputation emptySplitHashCache)
    hinitialClean (root, rootCache) hroot
  have hrootSynced := revealedSynced_of_mem_runDetailed_stateFree parameter table
    AdaptiveRevealProbe.State.empty rootState fuel emptySplitHashCache rootCache root
    (simulateQ ordinaryHashImpl rootComputation) hinitialClean
    (revealedSynced_empty parameter table)
    (simulateQ_ordinaryHashImpl_stateFree rootComputation)
    (simulateQ_ordinaryHashImpl_cachePreserving rootComputation) hroot
  have hrestLift := simulateQ_maskedExpandedAdversaryImpl_done_false
    maskedSecretKey table
    (tracedGameRestComputation adversary ⟨root, parameter⟩)
    rootState finalState fuel rootCache finalCache value hrootClean hrootSynced
    (by simpa [maskedSecretKey] using hrest)
  refine ⟨?_, hrestLift.2.1, hrestLift.2.2⟩
  rw [simulateQ_romImpl_gameAfterSecrets_eq_tracedGameRestComputation,
    StateT.run_bind, mem_support_bind_iff]
  refine ⟨(root, mergedCache parameter table rootCache), ?_, ?_⟩
  · simpa [rootComputation] using hrootActual
  · simpa [maskedSecretKey, secretKeyWithFtsTable] using hrestLift.1

end SphincsSecurity.Concrete.FtsProbeSimulation
