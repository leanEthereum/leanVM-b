import SphincsSecurity.Proof.FtsProbeGame
import VCVio.OracleComp.QueryTracking.SubSpec

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

noncomputable def RomOrdinaryOnly (parameter : PublicParameter)
    (table : Coordinate → Digest)
    (computation : OracleComp OracleWorld alpha) : Prop := by
  classical
  exact computation.IsQueryBoundP
    (fun input => match input with
      | .inl _ => False
      | .inr hashInput => NonOrdinaryInput parameter table hashInput) 0

theorem RomOrdinaryOnly.pure (parameter : PublicParameter) (table : Coordinate → Digest)
    (value : alpha) :
    RomOrdinaryOnly parameter table (pure value) := by
  simp [RomOrdinaryOnly]

theorem RomOrdinaryOnly.bind
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {left : OracleComp OracleWorld alpha} {next : alpha → OracleComp OracleWorld beta}
    (hleft : RomOrdinaryOnly parameter table left)
    (hnext : ∀ value, RomOrdinaryOnly parameter table (next value)) :
    RomOrdinaryOnly parameter table (left >>= next) := by
  classical
  unfold RomOrdinaryOnly at hleft hnext ⊢
  exact isQueryBoundP_bind (n := 0) (m := 0) hleft fun value _ => hnext value

theorem OrdinaryOnly.liftRom
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {computation : OracleComp HashSpec alpha}
    (hordinary : OrdinaryOnly parameter table computation) :
    RomOrdinaryOnly parameter table
      (liftM computation : OracleComp OracleWorld alpha) := by
  classical
  unfold OrdinaryOnly at hordinary
  unfold RomOrdinaryOnly
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (h := OracleQuery.subSpec_add_right)
    (q := fun input : OracleWorld.Domain => match input with
      | .inl _ => False
      | .inr hashInput => NonOrdinaryInput parameter table hashInput)
    (fun _input => Iff.rfl) hordinary

theorem romOrdinaryOnly_liftProbComp
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (computation : ProbComp alpha) :
    RomOrdinaryOnly parameter table
      (liftM computation : OracleComp OracleWorld alpha) := by
  classical
  unfold RomOrdinaryOnly
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (h := OracleQuery.subSpec_add_left)
    (p := fun _ : unifSpec.Domain => False)
    (q := fun input : OracleWorld.Domain => match input with
      | .inl _ => False
      | .inr hashInput => NonOrdinaryInput parameter table hashInput)
    (fun _input => Iff.rfl) (isQueryBoundP_false computation 0)

theorem splitUniformImpl_stateFree (n : unifSpec.Domain) :
    StateFree (splitUniformImpl n) := by
  intro cache
  change (((fun output : Fin (n + 1) => (output, cache)) <$>
    AdaptiveRevealProbe.uniformQuery (Coordinate := Coordinate) n).IsQueryBoundP
      (AdaptiveRevealProbe.IsStateful (Coordinate := Coordinate)) 0)
  rw [isQueryBoundP_map_iff, AdaptiveRevealProbe.uniformQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [AdaptiveRevealProbe.IsStateful]

theorem simulateQ_splitRomImpl_stateFree
    (computation : OracleComp OracleWorld alpha) :
    StateFree (simulateQ splitRomImpl computation) := by
  intro cache
  apply (isQueryBoundP_false computation 0).simulateQ_run_StateT_of_step
  intro input workingCache
  cases input with
  | inl n => exact splitUniformImpl_stateFree n workingCache
  | inr hashInput => exact splitHashQuery_stateFree (.ordinary hashInput) workingCache

theorem splitUniformImpl_cachePreserving (n : unifSpec.Domain) :
    CachePreserving (splitUniformImpl n) := by
  intro initial result hresult
  unfold splitUniformImpl at hresult
  rw [StateT.run_liftM, mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  exact SplitCacheLE.refl initial

theorem simulateQ_splitRomImpl_cachePreserving
    (computation : OracleComp OracleWorld alpha) :
    CachePreserving (simulateQ splitRomImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact CachePreserving.pure value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      cases input with
      | inl n =>
          exact (splitUniformImpl_cachePreserving n).bind fun output => ih output
      | inr hashInput =>
          exact (splitHashQuery_cachePreserving (.ordinary hashInput)).bind
            fun output => ih output

theorem coupled_splitUniformImpl
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (n : unifSpec.Domain)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    Coupled parameter table state fuel (splitUniformImpl n) (unifFwdImpl HashSpec n) := by
  intro cache
  unfold splitUniformImpl
  rw [StateT.run_liftM]
  change projectDetailedCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state fuel
        ((liftM (OracleSpec.query (spec := AdaptiveRevealProbe.World Coordinate)
          (.uniform n)) : OracleComp (AdaptiveRevealProbe.World Coordinate) (Fin (n + 1))) >>=
            fun output => pure (output, cache)) = _
  rw [AdaptiveRevealProbe.runDetailed_uniform_query_bind]
  simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hclean, unifFwdImpl]

theorem coupled_simulateQ_splitRomImpl
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (computation : OracleComp OracleWorld alpha)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hordinaryOnly : RomOrdinaryOnly parameter table computation) :
    Coupled parameter table state fuel (simulateQ splitRomImpl computation)
      (simulateQ romImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact Coupled.pure parameter table state fuel hclean value
  | query_bind input next ih =>
      unfold RomOrdinaryOnly at hordinaryOnly
      rw [isQueryBoundP_query_bind_iff] at hordinaryOnly
      rw [simulateQ_query_bind, simulateQ_query_bind]
      cases input with
      | inl n =>
          refine Coupled.bind hclean (splitUniformImpl_stateFree n)
            (coupled_splitUniformImpl parameter table state fuel n hclean) ?_
          intro output
          exact ih output (by simpa [RomOrdinaryOnly] using hordinaryOnly.2 output)
      | inr input =>
          have hordinary : IsOrdinaryInput parameter table input := by
            by_contra hnot
            have hzero := hordinaryOnly.1
            simp [NonOrdinaryInput, hnot] at hzero
          refine Coupled.bind hclean (splitHashQuery_stateFree (.ordinary input))
            (coupled_splitHashQuery_ordinary parameter table state fuel input hclean
              hordinary) ?_
          intro output
          exact ih output (by
            simpa [RomOrdinaryOnly, NonOrdinaryInput, hordinary] using
              hordinaryOnly.2 output)

theorem ordinaryOnly_messageDigest
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (root : Digest) (message : Message) (randomness : Randomness) :
    OrdinaryOnly parameter table
      (messageDigest parameter root message randomness :
        OracleComp HashSpec MessageDigest) := by
  unfold messageDigest oracleHash OrdinaryOnly
  change ((liftM (HashSpec.query (tweakableHashInput parameter .message
    (messageDigestPayload root message randomness))) : OracleComp HashSpec HashOutput) >>=
      fun output => pure (truncateMessageDigest output)).IsQueryBoundP
        (NonOrdinaryInput parameter table) 0
  rw [isQueryBoundP_query_bind_iff]
  constructor
  · have hordinary : IsOrdinaryInput parameter table
        (tweakableHashInput parameter .message
          (messageDigestPayload root message randomness)) :=
      isOrdinaryInput_of_domain_ne_ftsLeaf parameter table .message _ (by trivial)
        (by intros; simp)
    simp [NonOrdinaryInput, hordinary]
  · intro output
    trivial

theorem ordinaryOnly_signAttempt
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (message : Message) (randomness : Randomness) :
    OrdinaryOnly secretKey.parameter table
      (signAttempt secretKey message randomness :
        OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) := by
  unfold signAttempt
  exact (ordinaryOnly_messageDigest secretKey.parameter table secretKey.root message
    randomness).bind fun digest => by
      split <;> exact OrdinaryOnly.pure secretKey.parameter table _

theorem romOrdinaryOnly_signDigestLoop
    (attempts : Nat) (secretKey : SecretKey) (table : Coordinate → Digest)
    (message : Message) :
    RomOrdinaryOnly secretKey.parameter table
      (signDigestLoop attempts secretKey message) := by
  induction attempts with
  | zero =>
      rw [signDigestLoop]
      exact RomOrdinaryOnly.pure secretKey.parameter table none
  | succ attempts ih =>
      rw [signDigestLoop]
      exact (romOrdinaryOnly_liftProbComp secretKey.parameter table sampleRandomness).bind
        fun randomness =>
          (ordinaryOnly_signAttempt secretKey table message randomness).liftRom.bind
            fun attempt => by
              cases attempt with
              | none => exact ih
              | some selected =>
                  exact RomOrdinaryOnly.pure secretKey.parameter table
                    (some (randomness, selected.1, selected.2))

theorem signAttempt_secretKeyWithFtsTable
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (message : Message) (randomness : Randomness) :
    (signAttempt (secretKeyWithFtsTable secretKey table) message randomness :
      OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) =
    signAttempt secretKey message randomness := by
  unfold signAttempt messageDigest oracleHash
  simp only [secretKeyWithFtsTable_parameter, secretKeyWithFtsTable_root]

theorem signDigestLoop_secretKeyWithFtsTable
    (attempts : Nat) (secretKey : SecretKey) (table : Coordinate → Digest)
    (message : Message) :
    signDigestLoop attempts (secretKeyWithFtsTable secretKey table) message =
      signDigestLoop attempts secretKey message := by
  induction attempts with
  | zero => rw [signDigestLoop, signDigestLoop]
  | succ attempts ih =>
      rw [signDigestLoop, signDigestLoop]
      simp only [signAttempt_secretKeyWithFtsTable, ih]

theorem hiddenIndexCached_of_mem_runDetailed_revealFtsSecret
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (initial final : SplitHashCache) (coordinate : Coordinate) (value : Digest)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state initial)
    (hcached : HiddenIndexCached index initial)
    (hcoordinate : coordinate.1 = index)
    (hresult : .done false finalState (value, final) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((revealFtsSecret parameter coordinate).run initial))) :
    HiddenIndexCached index final := by
  rcases coordinate with ⟨coordinateIndex, tree, leafIdx⟩
  simp only at hcoordinate
  subst coordinateIndex
  have hhidden := hcached tree leafIdx
  cases hrevealed : state.revealed (index, tree, leafIdx) with
  | none =>
      obtain ⟨output, hhiddenCache⟩ := hhidden
      have hrun := runDetailed_revealFtsSecret_hidden parameter table state fuel initial
        (index, tree, leafIdx) output hrevealed hclean hhiddenCache
      rw [hrun] at hresult
      simp only [support_pure, Set.mem_singleton_iff,
        AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      obtain ⟨hfinalState, hvalueCache⟩ := hresult.2
      subst finalState
      cases hvalueCache
      intro tree leafIdx
      obtain ⟨oldOutput, hold⟩ := hcached tree leafIdx
      refine ⟨oldOutput, ?_⟩
      rw [Function.update_of_ne (by simp)]
      exact hold
  | some revealedValue =>
      obtain ⟨hvalue, output, hhiddenCache, hordinaryCache⟩ :=
        hsynced (index, tree, leafIdx) revealedValue hrevealed
      have hrun := runDetailed_revealFtsSecret_revealed parameter table state fuel initial
        (index, tree, leafIdx) revealedValue output hrevealed hvalue hhiddenCache
        hordinaryCache hclean
      rw [hrun] at hresult
      simp only [support_pure, Set.mem_singleton_iff,
        AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
      obtain ⟨hfinalState, hvalueCache⟩ := hresult.2
      subst finalState
      cases hvalueCache
      exact hcached

theorem sequenceFin_pure_queryCache_run {n : Nat} (values : Fin n → alpha)
    (cache : QueryCache HashSpec) :
    (sequenceFin (fun position =>
      (pure (values position) : StateT (QueryCache HashSpec) ProbComp alpha))).run cache =
      pure (values, cache) := by
  induction n with
  | zero =>
      rw [sequenceFin, StateT.run_pure]
      congr 2
      funext position
      exact position.elim0
  | succ n ih =>
      rw [sequenceFin, StateT.run_bind, StateT.run_pure, pure_bind,
        StateT.run_bind, ih (fun position => values position.succ), pure_bind,
        StateT.run_pure]
      congr 2
      funext position
      cases position using Fin.cases <;> rfl

theorem tableHits_false_of_mem_runDetailed_probeFree
    (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) alpha)
    (hbound : computation.IsQueryBoundP AdaptiveRevealProbe.IsProbe 0)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (value : alpha)
    (hresult : .done false finalState value ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel computation)) :
    AdaptiveRevealProbe.tableHits finalState table = false := by
  obtain ⟨resultState, resultValue, hresultEq, hresultClean⟩ :=
    AdaptiveRevealProbe.runDetailed_probeFree_support table state fuel computation hbound
      hclean (.done false finalState value) hresult
  have hstate : finalState = resultState :=
    (AdaptiveRevealProbe.DetailedResult.done.inj hresultEq).2.1
  subst finalState
  exact hresultClean

theorem coupledAt_revealSequence {n : Nat}
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index)
    (coordinates : Fin n → Coordinate)
    (hcoordinates : ∀ position, (coordinates position).1 = index)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hcached : HiddenIndexCached index cache) :
    CoupledAt parameter table state fuel
      (sequenceFin fun position => revealFtsSecret parameter (coordinates position))
      (sequenceFin fun position =>
        (pure (table (coordinates position)) :
          StateT (QueryCache HashSpec) ProbComp Digest)) cache := by
  induction n generalizing state cache with
  | zero =>
      simp only [sequenceFin]
      exact (Coupled.pure parameter table state fuel hclean Fin.elim0).coupledAt cache
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
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
      apply CoupledAt.bind_probeFree hclean
        (revealFtsSecret_probeFree parameter (coordinates 0))
        (coupledAt_revealFtsSecret parameter table state fuel cache (coordinates 0) hclean
          hsynced hhiddenZero)
      intro headState headValue headCache hhead
      have hheadClean : AdaptiveRevealProbe.tableHits headState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table state headState fuel
          ((revealFtsSecret parameter (coordinates 0)).run cache)
          (revealFtsSecret_probeFree parameter (coordinates 0) cache) hclean
          (headValue, headCache) hhead
      have hheadSynced : RevealedSynced parameter table headState headCache :=
        revealedSynced_of_mem_runDetailed_revealFtsSecret parameter table state headState fuel
          cache headCache (coordinates 0) headValue hclean hsynced
          (hhiddenZero) hhead
      have hheadCached : HiddenIndexCached index headCache :=
        hiddenIndexCached_of_mem_runDetailed_revealFtsSecret parameter table index state
          headState fuel cache headCache (coordinates 0) headValue hclean hsynced hcached
          (hcoordinates 0) hhead
      apply CoupledAt.bind_probeFree hheadClean
        (sequenceFin_probeFree
          (fun position => revealFtsSecret parameter (coordinates position.succ))
          (fun position => revealFtsSecret_probeFree parameter (coordinates position.succ)))
        (ih (fun position => coordinates position.succ)
          (fun position => hcoordinates position.succ) headState headCache hheadClean
          hheadSynced hheadCached)
      intro tailState tailValue tailCache htail
      have htailClean : AdaptiveRevealProbe.tableHits tailState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table headState tailState fuel
          ((sequenceFin fun position =>
            revealFtsSecret parameter (coordinates position.succ)).run headCache)
          (sequenceFin_probeFree
            (fun position => revealFtsSecret parameter (coordinates position.succ))
            (fun position => revealFtsSecret_probeFree parameter
              (coordinates position.succ)) headCache)
          hheadClean (tailValue, tailCache) htail
      unfold CoupledAt
      simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, htailClean]

theorem coupledAt_revealSelectedFtsSecrets
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hcached : HiddenIndexCached index cache) :
    CoupledAt parameter table state fuel (revealSelectedFtsSecrets parameter index leaves)
      (pure (fun tree => table (index, tree, leaves (ftsIndexOf tree))) :
        StateT (QueryCache HashSpec) ProbComp (FtsTree → Digest)) cache := by
  unfold revealSelectedFtsSecrets
  have hcoupled := coupledAt_revealSequence parameter table index
    (fun tree => (index, tree, leaves (ftsIndexOf tree))) (fun tree => rfl)
    state fuel cache hclean hsynced hcached
  unfold CoupledAt at hcoupled ⊢
  rw [sequenceFin_pure_queryCache_run] at hcoupled
  exact hcoupled

theorem coupledAt_maskedSignAfterDigest
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache) :
    CoupledAt secretKey.parameter table state fuel
      (maskedSignAfterDigest secretKey randomness index leaves)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAfterDigest (secretKeyWithFtsTable secretKey table) randomness index leaves))
      cache := by
  unfold maskedSignAfterDigest signAfterDigest
  rw [simulateQ_bind]
  apply CoupledAt.bind_probeFree hclean
    (maskedFtsOpen_probeFree secretKey.parameter index leaves)
    ((coupled_maskedFtsOpen secretKey.parameter table state fuel index leaves hclean).coupledAt
      cache)
  intro pathState ftsPath pathCache hpath
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
  rw [simulateQ_bind, simulateQ_randomOracle_sequenceFin]
  apply CoupledAt.bind_probeFree hpathClean
    (sequenceFin_probeFree (fun lay => maskedSignLayer secretKey index lay)
      (fun lay => maskedSignLayer_probeFree secretKey index lay))
    ((coupled_sequenceFin secretKey.parameter table pathState fuel
      (fun lay => maskedSignLayer secretKey index lay)
      (fun lay => simulateQ (randomOracle : QueryImpl HashSpec _)
        (signLayer (secretKeyWithFtsTable secretKey table) index lay)) hpathClean
      (fun lay => maskedSignLayer_stateFree secretKey index lay)
      (fun lay => coupled_maskedSignLayer secretKey table pathState fuel index lay
        hpathClean)).coupledAt pathCache)
  intro layersState layers layersCache hlayers
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
      simp only [simulateQ_pure]
      unfold CoupledAt
      simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hlayersClean]
  | some parts =>
      simp only [simulateQ_pure]
      let finish := fun selected : FtsTree → Digest => some (show Signature from
        { randomness := randomness
          ftsSecret := selected
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (parts lay).2.1
          authPath := flattenPaths fun lay => (parts lay).2.2 })
      change CoupledAt secretKey.parameter table layersState fuel
        (revealSelectedFtsSecrets secretKey.parameter index leaves >>= fun selected =>
          pure (finish selected))
        ((pure (fun tree => table (index, tree, leaves (ftsIndexOf tree))) :
            StateT (QueryCache HashSpec) ProbComp (FtsTree → Digest)) >>= fun selected =>
          pure (finish selected)) layersCache
      apply CoupledAt.bind_probeFree hlayersClean
        (revealSelectedFtsSecrets_probeFree secretKey.parameter index leaves)
        (coupledAt_revealSelectedFtsSecrets secretKey.parameter table index leaves layersState
          fuel layersCache hlayersClean hlayersSynced hlayersCached)
      intro selectedState selected selectedCache hselected
      have hselectedClean : AdaptiveRevealProbe.tableHits selectedState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table layersState selectedState fuel
          ((revealSelectedFtsSecrets secretKey.parameter index leaves).run layersCache)
          (revealSelectedFtsSecrets_probeFree secretKey.parameter index leaves layersCache)
          hlayersClean (selected, selectedCache) hselected
      unfold CoupledAt
      simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hselectedClean]

set_option maxRecDepth 10000 in
theorem coupledAt_maskedSignWithView
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (message : Message)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache) :
    CoupledAt secretKey.parameter table state fuel
      (maskedSignWithView secretKey message)
      (simulateQ romImpl (signWithView (secretKeyWithFtsTable secretKey table) message))
      cache := by
  unfold maskedSignWithView signWithView
  rw [signDigestLoop_secretKeyWithFtsTable]
  rw [simulateQ_bind]
  apply CoupledAt.bind_probeFree hclean
    (simulateQ_splitRomImpl_probeFree
      (signDigestLoop digestAttemptLimit secretKey message))
    ((coupled_simulateQ_splitRomImpl secretKey.parameter table state fuel
      (signDigestLoop digestAttemptLimit secretKey message) hclean
      (romOrdinaryOnly_signDigestLoop digestAttemptLimit secretKey table message)).coupledAt
        cache)
  intro loopState selected loopCache hselected
  have hloopClean : AdaptiveRevealProbe.tableHits loopState table = false :=
    tableHits_false_of_mem_runDetailed_probeFree table state loopState fuel
      ((simulateQ splitRomImpl
        (signDigestLoop digestAttemptLimit secretKey message)).run cache)
      (simulateQ_splitRomImpl_probeFree
        (signDigestLoop digestAttemptLimit secretKey message) cache)
      hclean (selected, loopCache) hselected
  have hloopSynced : RevealedSynced secretKey.parameter table loopState loopCache :=
    revealedSynced_of_mem_runDetailed_stateFree secretKey.parameter table state loopState
      fuel cache loopCache selected
      (simulateQ splitRomImpl (signDigestLoop digestAttemptLimit secretKey message))
      hclean hsynced
      (simulateQ_splitRomImpl_stateFree
        (signDigestLoop digestAttemptLimit secretKey message))
      (simulateQ_splitRomImpl_cachePreserving
        (signDigestLoop digestAttemptLimit secretKey message)) hselected
  cases selected with
  | none =>
      exact (Coupled.pure secretKey.parameter table loopState fuel hloopClean
        (none, none)).coupledAt loopCache
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      rw [simulateQ_bind]
      simp only [romImpl, QueryImpl.simulateQ_add_liftM_right, simulateQ_pure]
      apply CoupledAt.bind_probeFree hloopClean
        (maskedSignAfterDigest_probeFree secretKey randomness index leaves)
        (coupledAt_maskedSignAfterDigest secretKey table loopState fuel loopCache randomness
          index leaves hloopClean hloopSynced)
      intro signatureState signature signatureCache hsignature
      have hsignatureClean :
          AdaptiveRevealProbe.tableHits signatureState table = false :=
        tableHits_false_of_mem_runDetailed_probeFree table loopState signatureState fuel
          ((maskedSignAfterDigest secretKey randomness index leaves).run loopCache)
          (maskedSignAfterDigest_probeFree secretKey randomness index leaves loopCache)
          hloopClean (signature, signatureCache) hsignature
      unfold CoupledAt
      simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hsignatureClean]

set_option maxRecDepth 10000 in
theorem coupledAt_maskedSigningImpl
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache) (message : Message)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache) :
    CoupledAt secretKey.parameter table state fuel
      (maskedSigningImpl secretKey message)
      (simulateQ romImpl (scheme.sign (secretKeyWithFtsTable secretKey table) message))
      cache := by
  change CoupledAt secretKey.parameter table state fuel
    (maskedSigningImpl secretKey message)
    (simulateQ romImpl (sign (secretKeyWithFtsTable secretKey table) message)) cache
  rw [← signWithView_fst]
  unfold maskedSigningImpl
  rw [simulateQ_map, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply CoupledAt.bind_probeFree hclean
    (maskedSignWithView_probeFree secretKey message)
    (coupledAt_maskedSignWithView secretKey table state fuel cache message hclean hsynced)
  intro finalState result finalCache hresult
  have hfinalClean : AdaptiveRevealProbe.tableHits finalState table = false :=
    tableHits_false_of_mem_runDetailed_probeFree table state finalState fuel
      ((maskedSignWithView secretKey message).run cache)
      (maskedSignWithView_probeFree secretKey message cache) hclean
      (result, finalCache) hresult
  unfold CoupledAt
  simp [AdaptiveRevealProbe.runDetailed, projectDetailedCache, hfinalClean]

end SphincsSecurity.Concrete.FtsProbeSimulation
