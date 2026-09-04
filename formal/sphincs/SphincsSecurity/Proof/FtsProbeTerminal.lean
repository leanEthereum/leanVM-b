import SphincsSecurity.Proof.FtsProbeOrigin

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

theorem mergedCache_mono
    (parameter : PublicParameter) (table : Coordinate → Digest)
    {initial final : SplitHashCache} (hle : SplitCacheLE initial final) :
    mergedCache parameter table initial ≤ mergedCache parameter table final := by
  intro input output houtput
  unfold mergedCache at houtput ⊢
  cases hdecode : decodeProbe? parameter input with
  | none =>
      simp only [hdecode] at houtput ⊢
      exact hle _ output houtput
  | some probe =>
      simp only [hdecode] at houtput ⊢
      by_cases hhit : probe.candidate = table (probe.index, probe.tree, probe.leafIdx)
      · simp only [hhit, if_true] at houtput ⊢
        exact hle _ output houtput
      · simp only [hhit, if_false] at houtput ⊢
        exact hle _ output houtput

theorem simulateQ_probingHashImpl_cachePreserving
    (parameter : PublicParameter) (computation : OracleComp HashSpec alpha) :
    CachePreserving (simulateQ (probingHashImpl parameter) computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact CachePreserving.pure value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      exact (probingHashQuery_cachePreserving parameter input).bind fun output => ih output

theorem probingHashQuery_done_false_hit_revealed
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (input : HashInput) (output : HashOutput)
    (probe : FtsSecretProbe)
    (hdecode : decodeProbe? parameter input = some probe)
    (hhit : probe.Hits (fun index tree leafIdx => table (index, tree, leafIdx)))
    (hresult : .done false finalState (output, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((probingHashQuery parameter input).run cache))) :
    ∃ value, state.revealed (probe.index, probe.tree, probe.leafIdx) = some value := by
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
      cases hrevealed : state.revealed (probe.index, probe.tree, probe.leafIdx) with
      | some value => exact ⟨value, rfl⟩
      | none =>
          have hcandidate : table (probe.index, probe.tree, probe.leafIdx) = probe.candidate :=
            hhit
          have hforced := runDetailed_probingHashQuery_hidden_hit parameter table state remaining
            cache input probe hdecode hrevealed hcandidate
            (.done false finalState (output, finalCache)) hresult
          change false = true at hforced
          simp at hforced

def HiddenHitsRevealed (parameter : PublicParameter) (table : Coordinate → Digest)
    (f : QueryImpl HashSpec Id) (state : AdaptiveRevealProbe.State Coordinate)
    (computation : OracleComp HashSpec alpha) : Prop :=
  ∀ input, input ∈ queriedInputs f computation →
    ∀ probe, decodeProbe? parameter input = some probe →
      probe.Hits (fun index tree leafIdx => table (index, tree, leafIdx)) →
        ∃ value, state.revealed (probe.index, probe.tree, probe.leafIdx) = some value

set_option maxHeartbeats 800000 in
set_option maxRecDepth 20000 in
theorem hiddenHitsRevealed_of_mem_runDetailed
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec alpha)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (value : alpha)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hf : (mergedCache parameter table finalCache).AgreesWithFn f)
    (hresult : .done false finalState (value, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((simulateQ (probingHashImpl parameter) computation).run cache))) :
    HiddenHitsRevealed parameter table f state computation := by
  induction computation using OracleComp.inductionOn generalizing
      state fuel cache finalState finalCache with
  | pure result =>
      intro input hinput
      simp at hinput
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hresult
      cases hdecode : decodeProbe? parameter input with
      | none =>
          have hheadProbeFree : ProbeFree (probingHashQuery parameter input) := by
            intro workingCache
            rw [probingHashQuery_run_eq, hdecode]
            exact splitHashQuery_probeFree (.ordinary input) workingCache
          obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
            mem_support_runDetailed_bind_probeFree table state finalState fuel
              ((probingHashQuery parameter input).run cache)
              (fun result =>
                (simulateQ (probingHashImpl parameter) (next result.1)).run result.2)
              (hheadProbeFree cache) hclean (value, finalCache) hresult
          rcases queryResult with ⟨output, queryCache⟩
          have hstep := probingHashQuery_done_false_invariants parameter table state
            queryState fuel cache queryCache input output hclean hquery
          have hstepSynced := probingHashQuery_done_false_revealedSynced parameter table state
            queryState fuel cache queryCache input output hclean hsynced hquery
          have hrawTail := AdaptiveRevealProbe.mem_support_of_mem_runDetailed_done table
            queryState finalState fuel
            ((simulateQ (probingHashImpl parameter) (next output)).run queryCache)
            false (value, finalCache) hrest
          have hsplitLe : SplitCacheLE queryCache finalCache :=
            simulateQ_probingHashImpl_cachePreserving parameter (next output)
              queryCache (value, finalCache) hrawTail
          have hle := mergedCache_mono parameter table hsplitLe
          have hqueryActual := probingHashQuery_done_false_mem_ordinary parameter table state
            queryState fuel cache queryCache input output hclean hsynced hquery
          have hcached := randomOracle_run_output_cached input
            (mergedCache parameter table cache)
            (mergedCache parameter table queryCache) output hqueryActual
          have houtput : f input = output := hf (hle hcached)
          have htail := ih output queryState finalState fuel queryCache finalCache
            hstep.1 hstepSynced hf hrest
          intro target htarget probe htargetDecode hhit
          rw [queriedInputs_query_bind] at htarget
          rcases List.mem_cons.mp htarget with htarget | htarget
          · subst target
            rw [hdecode] at htargetDecode
            simp at htargetDecode
          · rw [houtput] at htarget
            obtain ⟨revealed, hrevealed⟩ := htail target htarget probe htargetDecode hhit
            exact ⟨revealed, by simpa [hstep.2] using hrevealed⟩
      | some decoded =>
          have hwhole : .done false finalState (value, finalCache) ∈ support
              (AdaptiveRevealProbe.runDetailed table state fuel
                ((probingHashQuery parameter input).run cache >>= fun result =>
                  (simulateQ (probingHashImpl parameter) (next result.1)).run result.2)) :=
            hresult
          rw [probingHashQuery_run_eq, hdecode] at hwhole
          change .done false finalState (value, finalCache) ∈ support
            (AdaptiveRevealProbe.runDetailed table state fuel
              ((liftM (OracleSpec.query
                (spec := AdaptiveRevealProbe.World Coordinate)
                (.probe (decoded.index, decoded.tree, decoded.leafIdx) decoded.candidate)) :
                  OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
                (splitHashQuery (.ordinary input)).run cache >>= fun result =>
                  (simulateQ (probingHashImpl parameter) (next result.1)).run result.2)) at hwhole
          rw [AdaptiveRevealProbe.runDetailed_probe_query_bind] at hwhole
          cases fuel with
          | zero => simp at hwhole
          | succ remaining =>
              cases hrevealed : state.revealed
                  (decoded.index, decoded.tree, decoded.leafIdx) with
              | none =>
                  simp only [hrevealed] at hwhole
                  by_cases hdecodedHit : table (decoded.index, decoded.tree, decoded.leafIdx) =
                      decoded.candidate
                  · have hpostClean := tableHits_false_of_mem_runDetailed_done_false table
                        (state.addPending
                          (decoded.index, decoded.tree, decoded.leafIdx) decoded.candidate)
                        finalState remaining
                        ((splitHashQuery (.ordinary input)).run cache >>= fun result =>
                          (simulateQ (probingHashImpl parameter) (next result.1)).run result.2)
                        (value, finalCache) hwhole
                    have hpostHit := AdaptiveRevealProbe.tableHits_addPending_eq_true state table
                      (decoded.index, decoded.tree, decoded.leafIdx) decoded.candidate hdecodedHit
                    rw [hpostHit] at hpostClean
                    simp at hpostClean
                  · have hpostClean := AdaptiveRevealProbe.tableHits_addPending_eq_false state
                        table (decoded.index, decoded.tree, decoded.leafIdx) decoded.candidate
                        hclean hdecodedHit
                    obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
                      mem_support_runDetailed_bind_probeFree table
                        (state.addPending
                          (decoded.index, decoded.tree, decoded.leafIdx) decoded.candidate)
                        finalState remaining ((splitHashQuery (.ordinary input)).run cache)
                        (fun result =>
                          (simulateQ (probingHashImpl parameter) (next result.1)).run result.2)
                        (splitHashQuery_probeFree (.ordinary input) cache)
                        hpostClean (value, finalCache) hwhole
                    rcases queryResult with ⟨output, queryCache⟩
                    have hqueryOriginal : .done false queryState (output, queryCache) ∈ support
                        (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                          ((probingHashQuery parameter input).run cache)) := by
                      rw [probingHashQuery_run_eq, hdecode]
                      change .done false queryState (output, queryCache) ∈ support
                        (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                          ((liftM (OracleSpec.query
                            (spec := AdaptiveRevealProbe.World Coordinate)
                            (.probe (decoded.index, decoded.tree, decoded.leafIdx)
                              decoded.candidate)) :
                              OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
                            (splitHashQuery (.ordinary input)).run cache))
                      rw [AdaptiveRevealProbe.runDetailed_probe_query_bind, hrevealed]
                      exact hquery
                    have hstep := probingHashQuery_done_false_invariants parameter table state
                      queryState (remaining + 1) cache queryCache input output hclean hqueryOriginal
                    have hstepSynced := probingHashQuery_done_false_revealedSynced parameter table
                      state queryState (remaining + 1) cache queryCache input output hclean hsynced
                      hqueryOriginal
                    have hrawTail := AdaptiveRevealProbe.mem_support_of_mem_runDetailed_done table
                      queryState finalState remaining
                      ((simulateQ (probingHashImpl parameter) (next output)).run queryCache)
                      false (value, finalCache) hrest
                    have hsplitLe : SplitCacheLE queryCache finalCache :=
                      simulateQ_probingHashImpl_cachePreserving parameter (next output)
                        queryCache (value, finalCache) hrawTail
                    have hle := mergedCache_mono parameter table hsplitLe
                    have hqueryActual := probingHashQuery_done_false_mem_ordinary parameter table
                      state queryState (remaining + 1) cache queryCache input output hclean hsynced
                      hqueryOriginal
                    have hcached := randomOracle_run_output_cached input
                      (mergedCache parameter table cache)
                      (mergedCache parameter table queryCache) output hqueryActual
                    have houtput : f input = output := hf (hle hcached)
                    have htail := ih output queryState finalState remaining queryCache finalCache
                      hstep.1 hstepSynced hf hrest
                    intro target htarget probe htargetDecode hhit
                    rw [queriedInputs_query_bind] at htarget
                    rcases List.mem_cons.mp htarget with htarget | htarget
                    · subst target
                      have hprobe : probe = decoded := Option.some.inj
                        (htargetDecode.symm.trans hdecode)
                      subst probe
                      exact (hdecodedHit hhit).elim
                    · rw [houtput] at htarget
                      obtain ⟨revealed, hrevealedTail⟩ :=
                        htail target htarget probe htargetDecode hhit
                      exact ⟨revealed, by simpa [hstep.2] using hrevealedTail⟩
              | some revealedValue =>
                  simp only [hrevealed] at hwhole
                  obtain ⟨queryState, queryResult, hquery, hrest⟩ :=
                    mem_support_runDetailed_bind_probeFree table state finalState remaining
                      ((splitHashQuery (.ordinary input)).run cache)
                      (fun result =>
                        (simulateQ (probingHashImpl parameter) (next result.1)).run result.2)
                      (splitHashQuery_probeFree (.ordinary input) cache)
                      hclean (value, finalCache) hwhole
                  rcases queryResult with ⟨output, queryCache⟩
                  have hqueryOriginal : .done false queryState (output, queryCache) ∈ support
                      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                        ((probingHashQuery parameter input).run cache)) := by
                    rw [probingHashQuery_run_eq, hdecode]
                    change .done false queryState (output, queryCache) ∈ support
                      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                        ((liftM (OracleSpec.query
                          (spec := AdaptiveRevealProbe.World Coordinate)
                          (.probe (decoded.index, decoded.tree, decoded.leafIdx)
                            decoded.candidate)) :
                            OracleComp (AdaptiveRevealProbe.World Coordinate) Unit) >>= fun _ =>
                          (splitHashQuery (.ordinary input)).run cache))
                    rw [AdaptiveRevealProbe.runDetailed_probe_query_bind, hrevealed]
                    exact hquery
                  have hstep := probingHashQuery_done_false_invariants parameter table state
                    queryState (remaining + 1) cache queryCache input output hclean hqueryOriginal
                  have hstepSynced := probingHashQuery_done_false_revealedSynced parameter table
                    state queryState (remaining + 1) cache queryCache input output hclean hsynced
                    hqueryOriginal
                  have hrawTail := AdaptiveRevealProbe.mem_support_of_mem_runDetailed_done table
                    queryState finalState remaining
                    ((simulateQ (probingHashImpl parameter) (next output)).run queryCache)
                    false (value, finalCache) hrest
                  have hsplitLe : SplitCacheLE queryCache finalCache :=
                    simulateQ_probingHashImpl_cachePreserving parameter (next output)
                      queryCache (value, finalCache) hrawTail
                  have hle := mergedCache_mono parameter table hsplitLe
                  have hqueryActual := probingHashQuery_done_false_mem_ordinary parameter table
                    state queryState (remaining + 1) cache queryCache input output hclean hsynced
                    hqueryOriginal
                  have hcached := randomOracle_run_output_cached input
                    (mergedCache parameter table cache)
                    (mergedCache parameter table queryCache) output hqueryActual
                  have houtput : f input = output := hf (hle hcached)
                  have htail := ih output queryState finalState remaining queryCache finalCache
                    hstep.1 hstepSynced hf hrest
                  intro target htarget probe htargetDecode hhit
                  rw [queriedInputs_query_bind] at htarget
                  rcases List.mem_cons.mp htarget with htarget | htarget
                  · subst target
                    have hprobe : probe = decoded := Option.some.inj
                      (htargetDecode.symm.trans hdecode)
                    subst probe
                    exact ⟨revealedValue, hrevealed⟩
                  · rw [houtput] at htarget
                    obtain ⟨revealed, hrevealedTail⟩ :=
                      htail target htarget probe htargetDecode hhit
                    exact ⟨revealed, by simpa [hstep.2] using hrevealedTail⟩

theorem verify_ftsLeaf_query_mem
    (f : QueryImpl HashSpec Id) (publicKey : PublicKey) (message : Message)
    (signature : Signature) (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest) (tree : FtsTree) :
    tweakableHashInput publicKey.parameter
        (.ftsLeaf (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)))
        (digestBytes (signature.ftsSecret tree)) ∈
      queriedInputs f
        (verify (m := OracleComp HashSpec) publicKey message signature) := by
  rw [verify_eq, queriedInputs_bind]
  apply List.mem_append_right
  rw [hdigest]
  simp only [hadmissible, not_true_eq_false, if_false, queriedInputs_bind]
  apply List.mem_append_left
  exact ftsRecover_leaf_query_mem f publicKey.parameter (digestIndex digest)
    (digestLeaves digest) signature.ftsSecret signature.ftsPath tree

theorem uncoveredFtsSecret_revealed_of_clean_verify
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (f : QueryImpl HashSpec Id) (root : Digest) (otsSecret :
      Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (message : Message) (signature : Signature) (log : QueryLog SigningSpec)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache finalCache : SplitHashCache) (verified : Bool)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hf : (mergedCache parameter table finalCache).AgreesWithFn f)
    (hverify : .done false finalState (verified, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((simulateQ (probingHashImpl parameter)
          (verify (m := OracleComp HashSpec) ⟨root, parameter⟩ message signature)).run cache)))
    (huncovered : UncoveredFtsSecret f (mergedCache parameter table finalCache)
      ⟨parameter, root, otsSecret,
        fun index tree leafIdx => table (index, tree, leafIdx)⟩
      log (digestIndex digest) (digestLeaves digest) signature.ftsSecret) :
    ∃ (probe : FtsSecretProbe) (revealedValue : Digest),
      probe.Hits (fun index tree leafIdx => table (index, tree, leafIdx))
        ∧ state.revealed (probe.index, probe.tree, probe.leafIdx) = some revealedValue
        ∧ ¬SignedFtsLeaf f (mergedCache parameter table finalCache)
          ⟨parameter, root, otsSecret,
            fun index tree leafIdx => table (index, tree, leafIdx)⟩
          log probe.index probe.tree probe.leafIdx := by
  obtain ⟨tree, hnotSigned, hsecret, _⟩ := huncovered
  let probe : FtsSecretProbe :=
    ⟨digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree),
      signature.ftsSecret tree⟩
  have hhit : probe.Hits
      (fun index tree leafIdx => table (index, tree, leafIdx)) := hsecret.symm
  have hquery : probe.input parameter ∈ queriedInputs f
      (verify (m := OracleComp HashSpec) ⟨root, parameter⟩ message signature) := by
    simp only [FtsSecretProbe.input, probe]
    exact verify_ftsLeaf_query_mem f ⟨root, parameter⟩ message signature digest
      hdigest hadmissible tree
  have hrevealed := hiddenHitsRevealed_of_mem_runDetailed parameter table f
    (verify (m := OracleComp HashSpec) ⟨root, parameter⟩ message signature)
    state finalState fuel cache finalCache verified hclean hsynced hf hverify
    (probe.input parameter) hquery probe (decodeProbe?_input parameter probe) hhit
  obtain ⟨revealedValue, hrevealed⟩ := hrevealed
  exact ⟨probe, revealedValue, hhit, hrevealed, by simpa [probe] using hnotSigned⟩

set_option maxRecDepth 20000 in
theorem clean_trace_verify_not_uncoveredFtsSecret
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (prefixFuel verifyFuel : Nat)
    (initialCache prefixCache finalCache : SplitHashCache)
    (prefixState finalState : AdaptiveRevealProbe.State Coordinate)
    (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool)
    (f : QueryImpl HashSpec Id)
    (hf : (mergedCache secretKey.parameter table finalCache).AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest secretKey.parameter secretKey.root forgery.message
        forgery.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hsynced : RevealedSynced secretKey.parameter table
      AdaptiveRevealProbe.State.empty initialCache)
    (hprefix : .done false prefixState ((forgery, log), prefixCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty prefixFuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          (signingTraceComputation computation)).run initialCache)))
    (hverify : .done false finalState (verified, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table prefixState verifyFuel
        ((simulateQ (probingHashImpl secretKey.parameter)
          (verify (m := OracleComp HashSpec)
            ⟨secretKey.root, secretKey.parameter⟩ forgery.message
              forgery.signature)).run prefixCache))) :
    ¬UncoveredFtsSecret f (mergedCache secretKey.parameter table finalCache)
      (secretKeyWithFtsTable secretKey table) log (digestIndex digest)
      (digestLeaves digest) forgery.signature.ftsSecret := by
  intro huncovered
  have hinitialClean : AdaptiveRevealProbe.tableHits
      (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = false := by
    simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]
  have hprefixLift := simulateQ_maskedExpandedAdversaryImpl_done_false secretKey table
    (signingTraceComputation computation) AdaptiveRevealProbe.State.empty prefixState prefixFuel
    initialCache prefixCache (forgery, log) hinitialClean hsynced hprefix
  have hrawVerify := AdaptiveRevealProbe.mem_support_of_mem_runDetailed_done table
    prefixState finalState verifyFuel
    ((simulateQ (probingHashImpl secretKey.parameter)
      (verify (m := OracleComp HashSpec)
        ⟨secretKey.root, secretKey.parameter⟩ forgery.message forgery.signature)).run
      prefixCache)
    false (verified, finalCache) hverify
  have hsplitLe : SplitCacheLE prefixCache finalCache :=
    simulateQ_probingHashImpl_cachePreserving secretKey.parameter
      (verify (m := OracleComp HashSpec)
        ⟨secretKey.root, secretKey.parameter⟩ forgery.message forgery.signature)
      prefixCache (verified, finalCache) hrawVerify
  have hle := mergedCache_mono secretKey.parameter table hsplitLe
  obtain ⟨probe, revealedValue, _, hrevealed, hnotSigned⟩ :=
    uncoveredFtsSecret_revealed_of_clean_verify secretKey.parameter table f
      secretKey.root secretKey.otsSecret forgery.message forgery.signature log digest
      hdigest hadmissible prefixState finalState verifyFuel prefixCache finalCache verified
      hprefixLift.2.1 hprefixLift.2.2 hf hverify (by
        simpa [secretKeyWithFtsTable] using huncovered)
  have hsigned := signedFtsLeaf_of_revealed_signingTraceComputation_at_reference
    secretKey table computation prefixFuel initialCache prefixCache prefixState forgery log hsynced
    (mergedCache secretKey.parameter table finalCache) hle f hf hprefix
    (probe.index, probe.tree, probe.leafIdx) revealedValue hrevealed
  exact hnotSigned hsigned

end SphincsSecurity.Concrete.FtsProbeSimulation
