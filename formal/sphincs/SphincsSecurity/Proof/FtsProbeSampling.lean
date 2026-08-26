import SphincsSecurity.Proof.FtsProbeProbability

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace Concrete.FtsProbeSimulation

attribute [local semireducible] sampleFtsSecrets

abbrev RetainedRestResult := (Forgery × QueryLog SigningSpec) × Bool

abbrev RetainedGameResult := Digest × RetainedRestResult

noncomputable def retainedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) RetainedRestResult := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure ((forgery, log), verified)

theorem retainedGameRestComputation_verdict_projection
    (adversary : Adversary) (publicKey : PublicKey) :
    (fun result : RetainedRestResult =>
      decide (SigningTranscript.Valid result.1.2 ∧
        ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2) <$>
        retainedGameRestComputation adversary publicKey =
      tracedGameRestComputation adversary publicKey := by
  simp [retainedGameRestComputation, tracedGameRestComputation]

theorem simulateQ_probingRomImpl_scheme_verify
    (parameter : PublicParameter) (publicKey : PublicKey)
    (message : Message) (signature : Signature) :
    simulateQ (probingRomImpl parameter)
        (scheme.verify publicKey message signature) =
      simulateQ (probingHashImpl parameter)
        (verify (m := OracleComp HashSpec) publicKey message signature) := by
  change simulateQ (splitUniformImpl + probingHashImpl parameter)
      (liftM (verify (m := OracleComp HashSpec) publicKey message signature)) = _
  exact QueryImpl.simulateQ_add_liftM_right _ _ _

theorem simulateQ_maskedExpanded_retainedGameRestComputation
    (adversary : Adversary) (secretKey : SecretKey) :
    simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
        (retainedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩) = (do
      let (forgery, log) ←
        simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          (signingTraceComputation
            (adversary.main ⟨secretKey.root, secretKey.parameter⟩))
      let verified ← simulateQ (probingHashImpl secretKey.parameter)
        (verify (m := OracleComp HashSpec)
          ⟨secretKey.root, secretKey.parameter⟩ forgery.message forgery.signature)
      pure ((forgery, log), verified)) := by
  unfold retainedGameRestComputation
  rw [simulateQ_bind]
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
    pure ((forgery, log), verified)) = _
  rw [simulateQ_liftOracleWorldLeft, simulateQ_probingRomImpl_scheme_verify]

theorem simulateQ_expanded_retainedGameRestComputation_isQueryBoundP
    (adversary : Adversary) (secretKey : SecretKey) (q : Nat)
    (hbound : (gameRest scheme adversary
      ⟨secretKey.root, secretKey.parameter⟩ secretKey).IsQueryBoundP
        (· matches Sum.inr _) q) :
    (simulateQ (expandedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary
        ⟨secretKey.root, secretKey.parameter⟩)).IsQueryBoundP
          (· matches Sum.inr _) q := by
  let verdict := fun result : RetainedRestResult =>
        decide (SigningTranscript.Valid result.1.2 ∧
          ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2
  have heq : verdict <$>
        simulateQ (expandedAdversaryImpl secretKey)
          (retainedGameRestComputation adversary
            ⟨secretKey.root, secretKey.parameter⟩) =
      simulateQ (expandedAdversaryImpl secretKey)
        (tracedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩) := by
            rw [← retainedGameRestComputation_verdict_projection]
            simp [verdict]
  have hmap : (verdict <$>
      simulateQ (expandedAdversaryImpl secretKey)
        (retainedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩)).IsQueryBoundP
            (· matches Sum.inr _) q := by
    rw [heq, simulateQ_expanded_tracedGameRestComputation adversary secretKey]
    exact hbound
  exact (isQueryBoundP_map_iff _ verdict q).mp hmap

noncomputable def maskedRetainedGameAfterSecrets (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) RetainedGameResult := do
  let root ← simulateQ ordinaryHashImpl
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
  let secretKey : SecretKey :=
    ⟨parameter, root, otsSecret, fun _index _tree _leafIdx => 0⟩
  let result ← simulateQ (maskedExpandedAdversaryImpl parameter secretKey)
    (retainedGameRestComputation adversary ⟨root, parameter⟩)
  pure (root, result)

noncomputable def actualRetainedGameAfterSecrets (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) :
    ProbComp (RetainedGameResult × QueryCache HashSpec) := do
  let (root, rootCache) ←
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅
  let secretKey : SecretKey :=
    ⟨parameter, root, otsSecret,
      fun index tree leafIdx => table (index, tree, leafIdx)⟩
  let (result, finalCache) ←
    (simulateQ (unloggedMappedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).run rootCache
  pure ((root, result), finalCache)

set_option maxRecDepth 30000 in
theorem relTriple_maskedRetainedGameAfterSecrets
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat)
    (hbound : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP
        (· matches Sum.inr _) q) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
        ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run
          emptySplitHashCache))
      (actualRetainedGameAfterSecrets adversary parameter otsSecret table)
      (CleanStepRel parameter table) := by
  let rootComputation : OracleComp HashSpec Digest :=
    treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)
  have hinitialClean : AdaptiveRevealProbe.tableHits
      (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = false := by
    simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]
  rw [maskedRetainedGameAfterSecrets, actualRetainedGameAfterSecrets,
    StateT.run_bind]
  apply relTriple_runDetailed_bind_cleanOnly parameter table
    AdaptiveRevealProbe.State.empty q
    ((simulateQ ordinaryHashImpl rootComputation).run emptySplitHashCache)
    (fun result =>
      let secretKey : SecretKey :=
        ⟨parameter, result.1, otsSecret, fun _index _tree _leafIdx => 0⟩
      ((simulateQ (maskedExpandedAdversaryImpl parameter secretKey)
        (retainedGameRestComputation adversary ⟨result.1, parameter⟩)).run result.2 >>= fun
          restResult => pure ((result.1, restResult.1), restResult.2)))
    ((simulateQ (randomOracle : QueryImpl HashSpec _) rootComputation).run ∅)
    (fun result =>
      let secretKey : SecretKey :=
        ⟨parameter, result.1, otsSecret,
          fun index tree leafIdx => table (index, tree, leafIdx)⟩
      ((simulateQ (unloggedMappedAdversaryImpl secretKey)
        (retainedGameRestComputation adversary ⟨result.1, parameter⟩)).run result.2 >>= fun
          restResult => pure ((result.1, restResult.1), restResult.2)))
    (simulateQ_ordinaryHashImpl_probeFree rootComputation emptySplitHashCache)
  · simpa using (relTriple_of_coupledAt_stateFree
      ((coupled_simulateQ_ordinaryHashImpl parameter table
        AdaptiveRevealProbe.State.empty q rootComputation hinitialClean
        (ordinaryOnly_treeRoot parameter table topLayer rootTree
          (otsSecret topLayer rootTree))).coupledAt emptySplitHashCache)
      hinitialClean (revealedSynced_empty parameter table)
      (simulateQ_ordinaryHashImpl_stateFree rootComputation)
      (simulateQ_ordinaryHashImpl_cachePreserving rootComputation))
  · intro finalState root finalCache hfinalClean hfinalSynced hright
    let maskedSecretKey : SecretKey :=
      ⟨parameter, root, otsSecret, fun _index _tree _leafIdx => 0⟩
    let actualSecretKey : SecretKey := secretKeyWithFtsTable maskedSecretKey table
    have hrootRun : root ∈ support
        ((simulateQ (randomOracle : QueryImpl HashSpec _) rootComputation).run' ∅) := by
      rw [StateT.run'_eq, support_map]
      exact ⟨(root, mergedCache parameter table finalCache), hright, rfl⟩
    have hroot : root ∈ support rootComputation :=
      OracleComp.support_simulateQ_run'_subset
        (randomOracle : QueryImpl HashSpec _) rootComputation ∅ hrootRun
    have hrootLift : root ∈ support
        (liftM rootComputation : OracleComp OracleWorld Digest) := by
      rw [← OracleComp.liftComp_eq_liftM,
        OracleComp.mem_support_liftComp_iff]
      exact hroot
    have hrest : (gameRest scheme adversary ⟨root, parameter⟩ actualSecretKey).IsQueryBoundP
        (· matches Sum.inr _) q := by
      apply isQueryBoundP_of_bind hbound root
      exact hrootLift
    have hretained :=
      simulateQ_expanded_retainedGameRestComputation_isQueryBoundP
        adversary actualSecretKey q hrest
    have hmapped : ((fun result : RetainedRestResult => (root, result)) <$>
        simulateQ (expandedAdversaryImpl actualSecretKey)
          (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
            (· matches Sum.inr _) q :=
      (isQueryBoundP_map_iff _ _ q).2 hretained
    have hmapped' : (simulateQ
        (expandedAdversaryImpl (secretKeyWithFtsTable maskedSecretKey table))
        ((fun result : RetainedRestResult => (root, result)) <$>
          retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
            (· matches Sum.inr _) q := by
      simpa [actualSecretKey] using hmapped
    simpa [maskedSecretKey, actualSecretKey, secretKeyWithFtsTable,
      simulateQ_map, StateT.run_map] using
      (relTriple_simulateQ_maskedExpandedAdversaryImpl maskedSecretKey table
        ((fun result : RetainedRestResult => (root, result)) <$>
          retainedGameRestComputation adversary ⟨root, parameter⟩)
        finalState q finalCache hmapped' hfinalClean hfinalSynced)

set_option maxRecDepth 30000 in
theorem runDetailed_retainedGameRestComputation_clean_decompose
    (adversary : Adversary) (secretKey : SecretKey)
    (table : Coordinate → Digest) (fuel : Nat)
    (initialCache finalCache : SplitHashCache)
    (finalState : AdaptiveRevealProbe.State Coordinate)
    (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool)
    (hresult : .done false finalState (((forgery, log), verified), finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty fuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          (retainedGameRestComputation adversary
            ⟨secretKey.root, secretKey.parameter⟩)).run initialCache))) :
    ∃ prefixState prefixFuel prefixCache verifyFuel,
      .done false prefixState ((forgery, log), prefixCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty prefixFuel
          ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
            (signingTraceComputation
              (adversary.main ⟨secretKey.root, secretKey.parameter⟩))).run initialCache)) ∧
      .done false finalState (verified, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table prefixState verifyFuel
          ((simulateQ (probingHashImpl secretKey.parameter)
            (verify (m := OracleComp HashSpec)
              ⟨secretKey.root, secretKey.parameter⟩
              forgery.message forgery.signature)).run prefixCache)) := by
  obtain ⟨rawResult, hraw, hfinalize⟩ :=
    AdaptiveRevealProbe.exists_mem_support_runRaw_of_mem_runDetailed table
      AdaptiveRevealProbe.State.empty fuel
      ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
        (retainedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩)).run initialCache)
      (.done false finalState (((forgery, log), verified), finalCache)) hresult
  cases rawResult with
  | stopped hit => simp [AdaptiveRevealProbe.RawResult.finalize] at hfinalize
  | done rawFinalState remaining value =>
      have hcleanFinal : AdaptiveRevealProbe.tableHits rawFinalState table = false :=
        (AdaptiveRevealProbe.DetailedResult.done.inj hfinalize).1
      have hstate : rawFinalState = finalState :=
        (AdaptiveRevealProbe.DetailedResult.done.inj hfinalize).2.1
      have hvalue : value = (((forgery, log), verified), finalCache) :=
        (AdaptiveRevealProbe.DetailedResult.done.inj hfinalize).2.2
      subst rawFinalState
      subst value
      rw [simulateQ_maskedExpanded_retainedGameRestComputation,
        StateT.run_bind, AdaptiveRevealProbe.runRaw_bind,
        mem_support_bind_iff] at hraw
      obtain ⟨prefixRaw, hprefixRaw, htailRaw⟩ := hraw
      cases prefixRaw with
      | stopped prefixHit => simp at htailRaw
      | done prefixState prefixFuel prefixValue =>
          rcases prefixValue with ⟨⟨prefixForgery, prefixLog⟩, prefixCache⟩
          simp only at htailRaw
          rw [StateT.run_bind, AdaptiveRevealProbe.runRaw_bind,
            mem_support_bind_iff] at htailRaw
          obtain ⟨verifyRaw, hverifyRaw, hfinishRaw⟩ := htailRaw
          cases verifyRaw with
          | stopped verifyHit => simp at hfinishRaw
          | done verifyState verifyFuel verifyValue =>
              rcases verifyValue with ⟨prefixVerified, prefixFinalCache⟩
              have hfinishEq :
                  AdaptiveRevealProbe.RawResult.done finalState remaining
                      (((forgery, log), verified), finalCache) =
                    AdaptiveRevealProbe.RawResult.done verifyState verifyFuel
                      (((prefixForgery, prefixLog), prefixVerified), prefixFinalCache) := by
                simpa [AdaptiveRevealProbe.runRaw] using hfinishRaw
              have hverifyState :=
                (AdaptiveRevealProbe.RawResult.done.inj hfinishEq).1
              have hverifyFuel :=
                (AdaptiveRevealProbe.RawResult.done.inj hfinishEq).2.1
              have hverifyOutput :=
                (AdaptiveRevealProbe.RawResult.done.inj hfinishEq).2.2
              subst verifyState
              subst verifyFuel
              have houter := Prod.mk.inj hverifyOutput
              have hinner := Prod.mk.inj houter.1
              have hforgeryLog := Prod.mk.inj hinner.1
              obtain ⟨hforgery, hlog⟩ := hforgeryLog
              have hverified := hinner.2
              have hcache := houter.2
              subst prefixForgery
              subst prefixLog
              subst prefixVerified
              subst prefixFinalCache
              have hverifyDetailed :
                  AdaptiveRevealProbe.DetailedResult.done false finalState
                    (verified, finalCache) ∈ support
                    (AdaptiveRevealProbe.runDetailed table prefixState prefixFuel
                      ((simulateQ (probingHashImpl secretKey.parameter)
                        (verify (m := OracleComp HashSpec)
                          ⟨secretKey.root, secretKey.parameter⟩
                          forgery.message forgery.signature)).run prefixCache)) := by
                rw [← AdaptiveRevealProbe.finalize_runRaw_eq_runDetailed, support_map]
                exact ⟨.done finalState remaining (verified, finalCache), hverifyRaw, by
                  simp [AdaptiveRevealProbe.RawResult.finalize, hcleanFinal]⟩
              have hprefixClean :
                  AdaptiveRevealProbe.tableHits prefixState table = false := by
                cases hhit : AdaptiveRevealProbe.tableHits prefixState table with
                | false => rfl
                | true =>
                    have hforced := runDetailed_hit_eq_true_of_tableHits_eq_true table
                      prefixState prefixFuel
                      ((simulateQ (probingHashImpl secretKey.parameter)
                        (verify (m := OracleComp HashSpec)
                          ⟨secretKey.root, secretKey.parameter⟩
                          forgery.message forgery.signature)).run prefixCache)
                      hhit (.done false finalState (verified, finalCache)) hverifyDetailed
                    change false = true at hforced
                    exact Bool.noConfusion hforced
              have hprefixDetailed :
                  AdaptiveRevealProbe.DetailedResult.done false prefixState
                    ((forgery, log), prefixCache) ∈ support
                    (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty
                      fuel
                      ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                        (signingTraceComputation
                          (adversary.main ⟨secretKey.root, secretKey.parameter⟩))).run
                            initialCache)) := by
                rw [← AdaptiveRevealProbe.finalize_runRaw_eq_runDetailed, support_map]
                exact ⟨.done prefixState prefixFuel ((forgery, log), prefixCache),
                  hprefixRaw, by
                    simp [AdaptiveRevealProbe.RawResult.finalize, hprefixClean]⟩
              exact ⟨prefixState, fuel, prefixCache, prefixFuel,
                hprefixDetailed, hverifyDetailed⟩

theorem runDetailed_retainedGameRestComputation_not_uncoveredFtsSecret
    (adversary : Adversary) (secretKey : SecretKey)
    (table : Coordinate → Digest) (fuel : Nat)
    (initialCache finalCache : SplitHashCache)
    (finalState : AdaptiveRevealProbe.State Coordinate)
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
    (hresult : .done false finalState (((forgery, log), verified), finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty fuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          (retainedGameRestComputation adversary
            ⟨secretKey.root, secretKey.parameter⟩)).run initialCache))) :
    ¬UncoveredFtsSecret f (mergedCache secretKey.parameter table finalCache)
      (secretKeyWithFtsTable secretKey table) log (digestIndex digest)
      (digestLeaves digest) forgery.signature.ftsSecret := by
  obtain ⟨prefixState, prefixFuel, prefixCache, verifyFuel, hprefix, hverify⟩ :=
    runDetailed_retainedGameRestComputation_clean_decompose adversary secretKey table fuel
      initialCache finalCache finalState forgery log verified hresult
  exact clean_trace_verify_not_uncoveredFtsSecret secretKey table
    (adversary.main ⟨secretKey.root, secretKey.parameter⟩) prefixFuel verifyFuel
    initialCache prefixCache finalCache prefixState finalState forgery log verified f hf
    digest hdigest hadmissible hsynced hprefix hverify

set_option maxRecDepth 30000 in
theorem runDetailed_maskedRetainedGameAfterSecrets_not_uncoveredFtsSecret
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (fuel : Nat)
    (finalState : AdaptiveRevealProbe.State Coordinate)
    (root : Digest) (forgery : Forgery) (log : QueryLog SigningSpec)
    (verified : Bool) (finalCache : SplitHashCache)
    (f : QueryImpl HashSpec Id)
    (hf : (mergedCache parameter table finalCache).AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter root forgery.message forgery.signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hresult : .done false finalState
      ((root, ((forgery, log), verified)), finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty fuel
          ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run
            emptySplitHashCache))) :
    ¬UncoveredFtsSecret f (mergedCache parameter table finalCache)
      ⟨parameter, root, otsSecret,
        fun index tree leafIdx => table (index, tree, leafIdx)⟩
      log (digestIndex digest) (digestLeaves digest) forgery.signature.ftsSecret := by
  let rootComputation : OracleComp HashSpec Digest :=
    treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)
  have hinitialClean : AdaptiveRevealProbe.tableHits
      (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table = false := by
    simp [AdaptiveRevealProbe.tableHits, AdaptiveRevealProbe.State.empty]
  rw [maskedRetainedGameAfterSecrets, StateT.run_bind] at hresult
  obtain ⟨rootState, rootValue, hroot, hrest⟩ :=
    mem_support_runDetailed_bind_probeFree table AdaptiveRevealProbe.State.empty
      finalState fuel
      ((simulateQ ordinaryHashImpl rootComputation).run emptySplitHashCache)
      (fun result =>
        let secretKey : SecretKey :=
          ⟨parameter, result.1, otsSecret, fun _index _tree _leafIdx => 0⟩
        ((simulateQ (maskedExpandedAdversaryImpl parameter secretKey)
          (retainedGameRestComputation adversary ⟨result.1, parameter⟩)).run result.2 >>= fun
            restResult => pure ((result.1, restResult.1), restResult.2)))
      (simulateQ_ordinaryHashImpl_probeFree rootComputation emptySplitHashCache)
      hinitialClean ((root, ((forgery, log), verified)), finalCache) hresult
  rcases rootValue with ⟨actualRoot, rootCache⟩
  obtain ⟨stateFreeValue, hstateFree⟩ :=
    AdaptiveRevealProbe.runDetailed_stateFree_support table
      AdaptiveRevealProbe.State.empty fuel
      ((simulateQ ordinaryHashImpl rootComputation).run emptySplitHashCache)
      (simulateQ_ordinaryHashImpl_stateFree rootComputation emptySplitHashCache)
      hinitialClean (.done false rootState (actualRoot, rootCache)) hroot
  have hrootState : rootState = AdaptiveRevealProbe.State.empty :=
    (AdaptiveRevealProbe.DetailedResult.done.inj hstateFree).2.1
  subst rootState
  let maskedSecretKey : SecretKey :=
    ⟨parameter, actualRoot, otsSecret, fun _index _tree _leafIdx => 0⟩
  let restRun :=
    (simulateQ (maskedExpandedAdversaryImpl parameter maskedSecretKey)
      (retainedGameRestComputation adversary ⟨actualRoot, parameter⟩)).run rootCache
  change .done false finalState ((root, ((forgery, log), verified)), finalCache) ∈ support
    (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty fuel
      ((fun result : RetainedRestResult × SplitHashCache =>
        ((actualRoot, result.1), result.2)) <$> restRun)) at hrest
  rw [AdaptiveRevealProbe.runDetailed_mapValue, support_map] at hrest
  obtain ⟨restResult, hrestResult, hrestEq⟩ := hrest
  cases restResult with
  | stopped hit => simp [AdaptiveRevealProbe.DetailedResult.mapValue] at hrestEq
  | done hit restState restValue =>
      rcases restValue with ⟨retainedResult, restCache⟩
      rcases retainedResult with ⟨⟨restForgery, restLog⟩, restVerified⟩
      change AdaptiveRevealProbe.DetailedResult.done hit restState
          ((actualRoot, ((restForgery, restLog), restVerified)), restCache) =
        AdaptiveRevealProbe.DetailedResult.done false finalState
          ((root, ((forgery, log), verified)), finalCache) at hrestEq
      have hhit := (AdaptiveRevealProbe.DetailedResult.done.inj hrestEq).1
      have hrestState := (AdaptiveRevealProbe.DetailedResult.done.inj hrestEq).2.1
      have hrestOutput := (AdaptiveRevealProbe.DetailedResult.done.inj hrestEq).2.2
      subst hit
      subst restState
      have houter := Prod.mk.inj hrestOutput
      have hrootRest := Prod.mk.inj houter.1
      have hretained := Prod.mk.inj hrootRest.2
      have hforgeryLog := Prod.mk.inj hretained.1
      have hrootEq := hrootRest.1
      have hcacheEq := houter.2
      have hforgeryEq := hforgeryLog.1
      have hlogEq := hforgeryLog.2
      have hverifiedEq := hretained.2
      subst actualRoot
      subst restForgery
      subst restLog
      subst restVerified
      subst restCache
      have hsynced : RevealedSynced parameter table
          AdaptiveRevealProbe.State.empty rootCache := by
        exact revealedSynced_of_mem_runDetailed_stateFree parameter table
          AdaptiveRevealProbe.State.empty AdaptiveRevealProbe.State.empty fuel
          emptySplitHashCache rootCache root
          (simulateQ ordinaryHashImpl rootComputation) hinitialClean
          (revealedSynced_empty parameter table)
          (simulateQ_ordinaryHashImpl_stateFree rootComputation)
          (simulateQ_ordinaryHashImpl_cachePreserving rootComputation) hroot
      have hnot := runDetailed_retainedGameRestComputation_not_uncoveredFtsSecret
        adversary maskedSecretKey table fuel rootCache finalCache finalState forgery log verified
        f (by simpa [maskedSecretKey] using hf) digest (by
          simpa [maskedSecretKey] using hdigest) hadmissible hsynced (by
            simpa [restRun, maskedSecretKey] using hrestResult)
      simpa [maskedSecretKey, secretKeyWithFtsTable] using hnot

def RetainedUncoveredFtsSecretWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest)
    (result : RetainedGameResult × QueryCache HashSpec) : Prop :=
  let root := result.1.1
  let forgery := result.1.2.1.1
  let log := result.1.2.1.2
  ∃ (f : QueryImpl HashSpec Id) (digest : MessageDigest),
    result.2.AgreesWithFn f ∧
      evalWithAnswerFn f
        (messageDigest parameter root forgery.message forgery.signature.randomness) = digest ∧
      Admissible digest ∧
      UncoveredFtsSecret f result.2
        ⟨parameter, root, otsSecret,
          fun index tree leafIdx => table (index, tree, leafIdx)⟩
        log (digestIndex digest) (digestLeaves digest) forgery.signature.ftsSecret

theorem probEvent_actualRetained_uncovered_le_detailed_hit
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (table : Coordinate → Digest) (q : Nat)
    (hbound : (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP
        (· matches Sum.inr _) q) :
    Pr[RetainedUncoveredFtsSecretWitness parameter otsSecret table |
        actualRetainedGameAfterSecrets adversary parameter otsSecret table] ≤
      Pr[fun result : AdaptiveRevealProbe.DetailedResult Coordinate
          (RetainedGameResult × SplitHashCache) => result.hit = true |
        AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
          ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run
            emptySplitHashCache)] := by
  let left := AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
    ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache)
  let right := actualRetainedGameAfterSecrets adversary parameter otsSecret table
  have hrel := relTriple_maskedRetainedGameAfterSecrets adversary parameter otsSecret table q
    hbound
  have hrelSupport := relTriple_and_left_support hrel
    (fun result => result ∈ support left) (fun result hresult => hresult)
  apply probEvent_le_of_relTriple (relTriple_symm hrelSupport)
  intro rightResult leftResult hrelation hevent
  rcases hrelation.1 with hhit | hclean
  · exact hhit
  · cases leftResult with
    | stopped hit => simp [CleanResultRel] at hclean
    | done hit finalState valueCache =>
        rcases valueCache with ⟨value, finalCache⟩
        simp only [CleanResultRel] at hclean
        obtain ⟨rfl, hright, _hfinalClean, _hfinalSynced⟩ := hclean
        subst rightResult
        rcases value with ⟨root, ⟨⟨forgery, log⟩, verified⟩⟩
        rcases hevent with ⟨f, digest, hf, hdigest, hadmissible, huncovered⟩
        have hnot :=
          runDetailed_maskedRetainedGameAfterSecrets_not_uncoveredFtsSecret adversary
            parameter otsSecret table q finalState root forgery log verified finalCache f hf
            digest hdigest hadmissible hrelation.2
        exact (hnot huncovered).elim

noncomputable def sampledActualRetainedFts (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    ProbComp ((Coordinate → Digest) × (RetainedGameResult × QueryCache HashSpec)) := do
  let table ← AdaptiveRevealProbe.sampleTable (Coordinate := Coordinate)
  let result ← actualRetainedGameAfterSecrets adversary parameter otsSecret table
  pure (table, result)

def SampledRetainedUncoveredFtsSecretWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (result : (Coordinate → Digest) × (RetainedGameResult × QueryCache HashSpec)) : Prop :=
  RetainedUncoveredFtsSecretWitness parameter otsSecret result.1 result.2

theorem mem_support_sampleFtsSecrets
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ftsSecret ∈ support sampleFtsSecrets := by
  change ftsSecret ∈ support
    (@SampleableType.selectElem (Index → FtsTree → FtsLeaf → Digest)
      ftsSecretsSampleableType)
  exact ftsSecretsSampleableType.mem_support_selectElem ftsSecret

set_option maxRecDepth 30000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledActualRetainedFts_uncovered_le
    (adversary : Adversary) (parameter : PublicParameter)
    (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) :
    Pr[SampledRetainedUncoveredFtsSecretWitness parameter otsSecret |
        sampledActualRetainedFts adversary parameter otsSecret] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  let maskedRun :=
    (maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache
  calc
    Pr[SampledRetainedUncoveredFtsSecretWitness parameter otsSecret |
        sampledActualRetainedFts adversary parameter otsSecret] ≤
      Pr[fun result : (Coordinate → Digest) ×
          AdaptiveRevealProbe.DetailedResult Coordinate
            (RetainedGameResult × SplitHashCache) => result.2.hit = true |
        AdaptiveRevealProbe.detailedExperiment AdaptiveRevealProbe.State.empty q
          maskedRun] := by
      unfold sampledActualRetainedFts AdaptiveRevealProbe.detailedExperiment
      apply probEvent_bind_le_bind_of_forall_le
      intro table _htable
      have hextend : AdaptiveRevealProbe.extendTable
          (AdaptiveRevealProbe.State.empty : AdaptiveRevealProbe.State Coordinate) table =
          table := by
        funext coordinate
        simp [AdaptiveRevealProbe.extendTable, AdaptiveRevealProbe.State.empty]
      rw [hextend]
      have hfts := mem_support_sampleFtsSecrets
        (fun index tree leafIdx => table (index, tree, leafIdx))
      have hbound := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
      simpa [SampledRetainedUncoveredFtsSecretWitness,
        AdaptiveRevealProbe.extendTable, AdaptiveRevealProbe.State.empty,
        probEvent_map, Function.comp_def, maskedRun] using
        (probEvent_actualRetained_uncovered_le_detailed_hit adversary parameter
          otsSecret table q hbound)
    _ = Pr[fun hit : Bool => hit = true |
        AdaptiveRevealProbe.experiment AdaptiveRevealProbe.State.empty q maskedRun] := by
      rw [← AdaptiveRevealProbe.detailedExperiment_hit_eq_experiment]
      rw [probEvent_map]
      rfl
    _ ≤ (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      letI : Nonempty Coordinate :=
        ⟨(⟨0, by norm_num [totalHeight]⟩,
          ⟨0, by norm_num [ftsTrees]⟩,
          ⟨0, by norm_num [ftsTreeHeight]⟩)⟩
      exact AdaptiveRevealProbe.experiment_empty_probability_le_unbounded q maskedRun

noncomputable def curryFtsTableEquiv :
    (Index → FtsTree → FtsLeaf → Digest) ≃ (Coordinate → Digest) where
  toFun table coordinate := table coordinate.1 coordinate.2.1 coordinate.2.2
  invFun table index tree leafIdx := table (index, tree, leafIdx)
  left_inv _ := rfl
  right_inv _ := rfl

theorem evalDist_uncurry_sampleFtsSecrets :
    𝒟[curryFtsTableEquiv <$> sampleFtsSecrets] =
      𝒟[AdaptiveRevealProbe.sampleTable (Coordinate := Coordinate)] := by
  letI : SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
    ftsSecretsSampleableType
  letI : SampleableType (Coordinate → Digest) :=
    AdaptiveRevealProbe.tableSampleableType
  apply evalDist_ext
  intro table
  change
    Pr[= table | curryFtsTableEquiv <$> ($ᵗ (Index → FtsTree → FtsLeaf → Digest))] =
      Pr[= table | $ᵗ (Coordinate → Digest)]
  exact probOutput_map_bijective_uniform_cross
    (Index → FtsTree → FtsLeaf → Digest) curryFtsTableEquiv
    curryFtsTableEquiv.bijective table

end Concrete.FtsProbeSimulation

end SphincsSecurity
