import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveProbability
import SphincsSecurity.Proof.OtsProbeResolvedCleanTerminal
import SphincsSecurity.Proof.OtsProbeResolvedDirectRecursive
import SphincsSecurity.Proof.TerminalResidual
import SphincsSecurity.Proof.FtsProbeSampling

/-!
# Clean terminal lift for adaptive one-time probes

The canonical delayed failure is transported to the uniformly completed clean interpreter. The
clean endpoint itself is already the generic `q * 2^-128` lazy-probe bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedTreeRoot
attribute [local semireducible] sampleOtsSecrets

noncomputable def constantDigestAnswer (digest : Digest) : QueryImpl HashSpec Id :=
  fun _ => hashOutputOfDigest digest

@[simp] theorem eval_tweakableHash_constantDigestAnswer
    (digest : Digest) (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    evalWithAnswerFn (constantDigestAnswer digest)
      (tweakableHash parameter domain payload) = digest := by
  rw [Concrete.eval_tweakableHash]
  exact truncateHash_hashOutputOfDigest digest

theorem eval_treeNode_constantDigestAnswer
    (digest : Digest) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) :
    ∀ level nodeIdx,
      evalWithAnswerFn (constantDigestAnswer digest)
        (treeNode parameter lay tree secret level nodeIdx) = digest := by
  intro level
  induction level with
  | zero =>
      intro nodeIdx
      rw [treeNode_zero_eq]
      simp only [evalWithAnswerFn_bind]
      exact eval_tweakableHash_constantDigestAnswer digest parameter _ _
  | succ level ih =>
      intro nodeIdx
      rw [treeNode_succ_eq]
      simp [evalWithAnswerFn_bind, ih]

theorem mem_support_treeRoot_all
    (digest : Digest) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) :
    digest ∈ support (treeRoot parameter lay tree secret : OracleComp HashSpec Digest) := by
  have hsim := (OracleComp.exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support
    (treeRoot parameter lay tree secret) ∅ digest).mp ⟨constantDigestAnswer digest,
      (by simp [QueryCache.AgreesWithFn]), by
        simp only [treeRoot]
        exact eval_treeNode_constantDigestAnswer digest parameter lay tree secret
          (layerHeight lay) 0⟩
  obtain ⟨cache, hcache⟩ := hsim
  apply OracleComp.support_simulateQ_run'_subset
    (randomOracle : QueryImpl HashSpec _) (treeRoot parameter lay tree secret) ∅
  rw [StateT.run'_eq, support_map]
  exact ⟨(digest, cache), hcache, rfl⟩

theorem isQueryBoundP_gameRest_all_roots
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) :
    (gameRest scheme adversary ⟨root, parameter⟩
      ⟨parameter, root, otsSecret, ftsSecret⟩).IsQueryBoundP
        (· matches Sum.inr _) q := by
  have hgame := Concrete.isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
  rw [Concrete.gameAfterSecrets] at hgame
  have hroot : root ∈ support
      (OracleComp.liftComp
        (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
          OracleComp HashSpec Digest)
        OracleWorld) := by
    rw [OracleComp.support_liftComp]
    exact mem_support_treeRoot_all root parameter topLayer rootTree
      (otsSecret topLayer rootTree)
  exact isQueryBoundP_of_bind hgame root (by
    simpa only [OracleComp.liftComp_eq_liftM] using hroot)

theorem mem_support_sampleOtsSecrets_all
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
    otsSecret ∈ support sampleOtsSecrets := by
  change otsSecret ∈ support
    (@SampleableType.selectElem
      (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
      otsSecretsSampleableType)
  exact otsSecretsSampleableType.mem_support_selectElem otsSecret

theorem isQueryBoundP_expandedRetained_all_tables_roots
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (root : Digest) :
    (simulateQ
      (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
      (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
        (· matches Sum.inr _) q := by
  let secretKey : SecretKey :=
    ⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩
  have hrest := isQueryBoundP_gameRest_all_roots adversary q hq parameter hparameter
    secretKey.otsSecret (mem_support_sampleOtsSecrets_all secretKey.otsSecret)
    ftsSecret hfts root
  have hbound :=
    Concrete.FtsProbeSimulation.simulateQ_expanded_retainedGameRestComputation_isQueryBoundP
      adversary secretKey q hrest
  convert hbound using 1 <;> rfl

noncomputable def rejectingHashOutput : HashOutput :=
  hashOutputCoordinatesEquiv.symm
    ((default, ⟨1, by norm_num [ftsTreeHeight]⟩), 0)

noncomputable def rejectingRomAnswer : QueryImpl OracleWorld Id
  | .inl n => (0 : Fin (n + 1))
  | .inr _ => rejectingHashOutput

theorem signAttemptResultOfOutput_rejecting :
    signAttemptResultOfOutput rejectingHashOutput = none := by
  by_contra h
  have hne : signAttemptResultOfOutput rejectingHashOutput ≠ none := h
  rw [show rejectingHashOutput = hashOutputCoordinatesEquiv.symm
      ((default, ⟨1, by norm_num [ftsTreeHeight]⟩), 0) from rfl,
    signAttemptResultOfOutput_coordinates_ne_none_iff] at hne
  norm_num at hne

@[simp] theorem eval_lift_hash_rejecting (input : HashInput) :
    evalWithAnswerFn rejectingRomAnswer
      (liftM (HashSpec.query input) : OracleComp OracleWorld HashOutput) =
        rejectingHashOutput := by
  rfl

theorem eval_lift_hash_comp_rejecting (computation : OracleComp HashSpec α) :
    evalWithAnswerFn rejectingRomAnswer
      (OracleComp.liftComp computation OracleWorld) =
        evalWithAnswerFn (fun _ : HashInput => rejectingHashOutput) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [OracleComp.liftComp_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
        show evalWithAnswerFn rejectingRomAnswer
          (OracleComp.liftComp (liftM (HashSpec.query input)) OracleWorld) =
            rejectingHashOutput from rfl,
        show
          evalWithAnswerFn (fun _ : HashInput => rejectingHashOutput)
            (liftM (HashSpec.query input)) = rejectingHashOutput from rfl]
      exact ih rejectingHashOutput

set_option maxRecDepth 100000 in
theorem eval_signAttempt_rejecting (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) :
    evalWithAnswerFn rejectingRomAnswer
      (liftM (signAttempt secretKey message randomness : OracleComp HashSpec _) :
        OracleComp OracleWorld _) = none := by
  change evalWithAnswerFn rejectingRomAnswer
    (OracleComp.liftComp (signAttempt secretKey message randomness : OracleComp HashSpec _)
      OracleWorld) = none
  rw [eval_lift_hash_comp_rejecting]
  simp only [signAttempt, messageDigest, oracleHash, evalWithAnswerFn_bind,
    evalWithAnswerFn_query, evalWithAnswerFn_pure]
  have hreject : ¬Admissible (truncateMessageDigest rejectingHashOutput) := by
    intro hadmissible
    have hne : signAttemptResultOfOutput rejectingHashOutput ≠ none :=
      (signAttemptResultOfOutput_ne_none_iff rejectingHashOutput).2 hadmissible
    exact hne signAttemptResultOfOutput_rejecting
  simp [hreject]

theorem eval_signDigestLoop_rejecting (attempts : Nat) (secretKey : SecretKey)
    (message : Message) :
    evalWithAnswerFn rejectingRomAnswer (signDigestLoop attempts secretKey message) = none := by
  induction attempts with
  | zero => simp [signDigestLoop]
  | succ attempts ih =>
      rw [signDigestLoop]
      simp only [evalWithAnswerFn_bind, eval_signAttempt_rejecting, ih]

theorem eval_sign_rejecting (secretKey : SecretKey) (message : Message) :
    evalWithAnswerFn rejectingRomAnswer (scheme.sign secretKey message) = none := by
  change evalWithAnswerFn rejectingRomAnswer (sign secretKey message) = none
  rw [sign_eq_digestLoop_afterDigest]
  simp [evalWithAnswerFn_bind, eval_signDigestLoop_rejecting]

theorem mem_support_sign_none (secretKey : SecretKey) (message : Message) :
    none ∈ support (scheme.sign secretKey message) := by
  have hsim := (OracleComp.exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support
    (scheme.sign secretKey message) ∅ none).mp
      ⟨rejectingRomAnswer, (by simp [QueryCache.AgreesWithFn]),
        eval_sign_rejecting secretKey message⟩
  obtain ⟨cache, hcache⟩ := hsim
  apply OracleComp.support_simulateQ_run'_subset
    (randomOracle : QueryImpl OracleWorld _) (scheme.sign secretKey message) ∅
  rw [StateT.run'_eq, support_map]
  exact ⟨(none, cache), hcache, rfl⟩

theorem mem_support_of_evalWithAnswerFn
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α)
    (value : α) (heval : evalWithAnswerFn f computation = value) :
    value ∈ support computation := by
  have hsim := (OracleComp.exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support
    computation ∅ value).mp ⟨f, (by simp [QueryCache.AgreesWithFn]), heval⟩
  obtain ⟨cache, hcache⟩ := hsim
  apply OracleComp.support_simulateQ_run'_subset
    (randomOracle : QueryImpl HashSpec _) computation ∅
  rw [StateT.run'_eq, support_map]
  exact ⟨(value, cache), hcache, rfl⟩

set_option maxRecDepth 100000 in
theorem SuccessfulSignRun.mem_support_sign
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f cache secretKey message signature) :
    some signature ∈ support (scheme.sign secretKey message) := by
  change some signature ∈ support (sign secretKey message)
  obtain ⟨index, leaves, hdigest, hafter⟩ := hrun.eval_signAfterDigest
  have hattempt : some (index, leaves) ∈
      support (signAttempt secretKey message signature.randomness : OracleComp HashSpec _) :=
    mem_support_of_evalWithAnswerFn f _ _ hdigest.2.1
  have hloop : some (signature.randomness, index, leaves) ∈
      support (signDigestLoop digestAttemptLimit secretKey message) := by
    rw [show digestAttemptLimit = (digestAttemptLimit - 1) + 1 by
      norm_num [digestAttemptLimit], signDigestLoop, mem_support_bind_iff]
    refine ⟨signature.randomness, ?_, ?_⟩
    · change signature.randomness ∈
        support (OracleComp.liftComp sampleRandomness OracleWorld)
      rw [OracleComp.mem_support_liftComp_iff]
      exact hdigest.1
    · rw [mem_support_bind_iff]
      refine ⟨some (index, leaves), ?_, by simp⟩
      change some (index, leaves) ∈ support
        (OracleComp.liftComp
          (signAttempt secretKey message signature.randomness : OracleComp HashSpec _)
          OracleWorld)
      rw [OracleComp.mem_support_liftComp_iff]
      exact hattempt
  have hafterSupport : some signature ∈
      support (signAfterDigest secretKey signature.randomness index leaves) :=
    mem_support_of_evalWithAnswerFn f _ _ hafter
  rw [sign_eq_digestLoop_afterDigest, mem_support_bind_iff]
  exact ⟨some (signature.randomness, index, leaves), hloop, by
    change some signature ∈ support
      (OracleComp.liftComp
        (signAfterDigest secretKey signature.randomness index leaves) OracleWorld)
    rw [OracleComp.mem_support_liftComp_iff]
    exact hafterSupport⟩

theorem tableOtsSecret_retainedCompletionTable_of_startTableAgrees
    (parameter : PublicParameter) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (table : OtsSecretIndex → HashOutput)
    (hagrees : StartTableAgrees state table) :
    tableOtsSecret (retainedCompletionTable parameter state cache
      (baseStartsOfTable table)) =
        tableOtsSecret (extendStartTable table) := by
  rw [tableOtsSecret_retainedCompletionTable_eq_extendStartTable]
  congr 2
  funext index
  unfold completedStartTable
  cases hvalue : state.values index.coordinate with
  | none => simp
  | some output => simp [hagrees index output hvalue]

set_option maxRecDepth 10000 in
theorem maskedSign_done_output_mem_support
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat)
    (output : Option Signature) (hagrees : StartTableAgrees finalState table)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining
        (output, finalCache) ∈ support
      (LazyRevealProbe.runRaw state fuel
        ((maskedSign parameter root ftsSecret message).run cache))) :
    output ∈ support
      (scheme.sign
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey)
        message) := by
  cases output with
  | none =>
      exact mem_support_sign_none _ _
  | some signature =>
      let baseStarts := fun lay tree leafIdx chainIdx =>
        table (⟨lay, tree, leafIdx, chainIdx⟩ : OtsSecretIndex)
      let completion := retainedCompletionTable parameter finalState finalCache baseStarts
      let f := retainedCompletionAnswer parameter finalState finalCache baseStarts
      have hrun := successfulSignRun_of_mem_runRaw_maskedSign f parameter root completion
        ftsSecret message signature state finalState cache finalCache fuel remaining finalState
          finalCache
          (stableCacheAgreesWithFn_retainedCompletionAnswer parameter finalState finalCache
            baseStarts)
          (fun coordinate cached hvalue =>
            (completedRealizedTable_of_value (splitFallback finalCache) parameter finalState
              baseStarts coordinate cached hvalue).symm)
          (retainedCompletionAnswer_realizes parameter finalState finalCache baseStarts)
          hresult (by intro coordinate hvalue; exact hvalue)
          (by intro input output hstable hcached; exact hcached)
      have hsupport := SuccessfulSignRun.mem_support_sign hrun
      have hsecret : tableOtsSecret completion =
          tableOtsSecret (extendStartTable table) := by
        change tableOtsSecret (retainedCompletionTable parameter finalState finalCache
          (baseStartsOfTable table)) = tableOtsSecret (extendStartTable table)
        exact tableOtsSecret_retainedCompletionTable_of_startTableAgrees parameter
          finalState finalCache table hagrees
      rw [hsecret] at hsupport
      exact hsupport

theorem startTableAgrees_completedStartTable
    (state : LazyRevealProbe.State Coordinate) (base : OtsSecretIndex → HashOutput) :
    StartTableAgrees state (completedStartTable state base) := by
  intro index output hvalue
  simp [completedStartTable, hvalue]

set_option maxRecDepth 100000 in
theorem stopped_false_not_mem_support_masked_adversary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache)
    (hbound : ∀ table : OtsSecretIndex → HashOutput,
      StartTableAgrees state table →
        (simulateQ
          (SphincsSecurity.expandedAdversaryImpl
            (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
          computation).IsQueryBoundP (· matches Sum.inr _) fuel) :
    LazyRevealProbe.RawResult.stopped false ∉ support
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          computation).run cache)) := by
  induction computation using OracleComp.inductionOn generalizing state fuel cache with
  | pure value => simp [simulateQ_pure, StateT.run_pure, LazyRevealProbe.runRaw]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        mem_support_bind_iff]
      rintro ⟨stepResult, hstep, htail⟩
      cases stepResult with
      | stopped hit =>
          cases hit with
          | false =>
              apply LazyRevealProbe.stopped_false_not_mem_support_runRaw state fuel
                ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run cache) ?_ hstep
              cases input with
              | inl worldInput =>
                  cases worldInput with
                  | inl n =>
                      exact (maskedExpandedAdversaryImpl_step_isProbeBound parameter root
                        ftsSecret (.inl (.inl n)) cache).mono (by simp [IsOuterHash])
                  | inr hashInput =>
                      let table := completedStartTable state (fun _ => 0)
                      have hsource := hbound table
                        (startTableAgrees_completedStartTable state _)
                      rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                        OracleComp.isQueryBoundP_query_bind_iff] at hsource
                      have hpositive : 0 < fuel := by simpa using hsource.1
                      exact (maskedExpandedAdversaryImpl_step_isProbeBound parameter root
                        ftsSecret (.inl (.inr hashInput)) cache).mono (by
                          simp [IsOuterHash]
                          omega)
              | inr message =>
                  exact (maskedExpandedAdversaryImpl_step_isProbeBound parameter root
                    ftsSecret (.inr message) cache).mono (by simp [IsOuterHash])
          | true => simp at htail
      | done finalState remaining result =>
          rcases result with ⟨output, finalCache⟩
          have hvaluesLE := LazyRevealProbe.valuesLE_of_mem_runRaw_done
            ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run cache)
            state finalState fuel remaining (output, finalCache) hstep
          have hinitial : ∀ table : OtsSecretIndex → HashOutput,
              StartTableAgrees finalState table → StartTableAgrees state table := by
            intro table hagrees index cached hcached
            exact hagrees index cached (hvaluesLE index.coordinate cached hcached)
          have hstepBound := maskedExpandedAdversaryImpl_step_isProbeBound parameter root
            ftsSecret input cache
          have hfuel := LazyRevealProbe.fuel_le_remaining_add_of_mem_support_runRaw_done
            state finalState fuel remaining (if IsOuterHash input then 1 else 0)
            ((maskedExpandedAdversaryImpl parameter root ftsSecret input).run cache)
            (output, finalCache) hstepBound hstep
          apply ih output finalState remaining finalCache
          · intro table hagrees
            have hsource := hbound table (hinitial table hagrees)
            cases input with
            | inl worldInput =>
                cases worldInput with
                | inl n =>
                    rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                      OracleComp.isQueryBoundP_query_bind_iff] at hsource
                    exact (hsource.2 output).mono (by simpa [IsOuterHash] using hfuel)
                | inr hashInput =>
                    rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                      OracleComp.isQueryBoundP_query_bind_iff] at hsource
                    have htailSource :
                        (simulateQ
                          (SphincsSecurity.expandedAdversaryImpl
                            (⟨parameter, root, tableOtsSecret (extendStartTable table),
                              ftsSecret⟩ : SecretKey))
                          (next output)).IsQueryBoundP (· matches Sum.inr _) (fuel - 1) := by
                      simpa using hsource.2 output
                    change fuel ≤ remaining + 1 at hfuel
                    exact htailSource.mono (by omega)
            | inr message =>
                change Option Signature at output
                change LazyRevealProbe.RawResult.done finalState remaining
                    (output, finalCache) ∈ support
                  (LazyRevealProbe.runRaw state fuel
                    ((maskedSigningImpl parameter root ftsSecret message).run cache)) at hstep
                rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hsource
                have houtput : output ∈ support
                    (scheme.sign
                      (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                        SecretKey) message) := by
                  exact maskedSign_done_output_mem_support parameter root table ftsSecret
                    message state finalState cache finalCache fuel remaining output hagrees
                      (by simpa only [SigningSpec, maskedExpandedAdversaryImpl,
                        maskedSigningImpl] using hstep)
                exact (isQueryBoundP_of_bind hsource output houtput).mono (by
                  simpa [IsOuterHash] using hfuel)
          · exact htail

noncomputable def chronologicalCleanRetainedRest
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (cache : SplitHashCache) :
    OracleComp (LazyRevealProbe.World Coordinate)
      (RetainedRestResult × SplitHashCache) :=
  (do
    let (forgery, log) ←
      simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (signingTraceComputation (adversary.main ⟨root, parameter⟩))
    let verified ← simulateQ (probingRomImpl parameter)
      (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
    pure ((forgery, log), verified)).run cache

noncomputable def chronologicalCleanRetainedRun
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    OracleComp (LazyRevealProbe.World Coordinate)
      (RetainedGameResult × SplitHashCache) := do
  let rootResult ← maskedPublishedTreeRoot.run emptySplitHashCache
  let restResult ← chronologicalCleanRetainedRest adversary parameter rootResult.1 ftsSecret
    rootResult.2
  pure ((rootResult.1, restResult.1), restResult.2)

noncomputable def deferredCleanRetainedRest
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (cache : SplitHashCache) :
    OracleComp (LazyRevealProbe.World Coordinate)
      (RetainedRestResult × SplitHashCache) :=
  (do
    let (forgery, log) ←
      simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
        (signingTraceComputation (adversary.main ⟨root, parameter⟩))
    let verified ← simulateQ (probingRomImpl parameter)
      (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
    pure ((forgery, log), verified)).run cache

noncomputable def deferredCleanRetainedRun
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    OracleComp (LazyRevealProbe.World Coordinate)
      (RetainedGameResult × SplitHashCache) := do
  let rootResult ← maskedPublishedTreeRoot.run emptySplitHashCache
  let restResult ← deferredCleanRetainedRest adversary parameter rootResult.1 ftsSecret
    rootResult.2
  pure ((rootResult.1, restResult.1), restResult.2)

set_option maxRecDepth 100000 in
theorem deferredCleanRetainedRun_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    deferredCleanRetainedRun adversary parameter ftsSecret =
      (maskedResolvedRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
        emptySplitHashCache := by
  unfold deferredCleanRetainedRun deferredCleanRetainedRest
    maskedResolvedRetainedGameAfterFtsSecrets maskedRetainedPrefixAfterFtsSecrets
  simp only [StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]

set_option maxRecDepth 100000 in
theorem chronologicalCleanRetainedRun_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    chronologicalCleanRetainedRun adversary parameter ftsSecret =
      (maskedChronologicalRetainedGameAfterFtsSecrets adversary parameter ftsSecret).run
        emptySplitHashCache := by
  unfold chronologicalCleanRetainedRun chronologicalCleanRetainedRest
    maskedChronologicalRetainedGameAfterFtsSecrets
    maskedChronologicalRetainedPrefixAfterFtsSecrets
  simp only [StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]

theorem maskedPublishedTreeRoot_probeFree : ProbeFree maskedPublishedTreeRoot := by
  intro cache
  rw [maskedPublishedTreeRoot_eq, StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (maskedTreeRoot_probeFree topLayer rootTree cache)
  intro rootResult _hroot
  rcases rootResult with ⟨root, nextCache⟩
  rw [StateT.run_bind]
  exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (publishCoordinate_probeFree (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))
        nextCache)
    (fun _ _ => by simp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
theorem stopped_false_not_mem_support_deferredCleanRetainedRun
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    LazyRevealProbe.RawResult.stopped false ∉ support
      (LazyRevealProbe.runRaw LazyRevealProbe.State.empty q
        (deferredCleanRetainedRun adversary parameter ftsSecret)) := by
  unfold deferredCleanRetainedRun
  apply LazyRevealProbe.stopped_false_not_mem_support_runRaw_bind_of_bound
  · exact maskedPublishedTreeRoot_probeFree emptySplitHashCache
  · apply LazyRevealProbe.stopped_false_not_mem_support_runRaw
    exact (maskedPublishedTreeRoot_probeFree emptySplitHashCache).mono (Nat.zero_le q)
  · intro rootState remaining rootResult _hroot hfuel
    rcases rootResult with ⟨root, cache⟩
    apply LazyRevealProbe.stopped_false_not_mem_support_runRaw_bind
    · unfold deferredCleanRetainedRest
      rw [← simulateQ_maskedExpanded_retainedGameRestComputation]
      apply stopped_false_not_mem_support_masked_adversary parameter root ftsSecret
        (retainedGameRestComputation adversary ⟨root, parameter⟩)
        rootState remaining cache
      intro table _hagrees
      exact (isQueryBoundP_expandedRetained_all_tables_roots adversary q hq parameter
        hparameter table ftsSecret hfts root).mono (by omega)
    · intro finalState finalRemaining restResult _hrest
      simp [LazyRevealProbe.runRaw]

theorem probEvent_sampledDeferredCleanFinish_none_le
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[= none | sampledRunThenFinalizeClean
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
        (deferredCleanRetainedRun adversary parameter ftsSecret)] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  probEvent_sampledRunThenFinalizeClean_empty_none_le_of_not_stopped_false
    (deferredCleanRetainedRun adversary parameter ftsSecret) q
      (stopped_false_not_mem_support_deferredCleanRetainedRun adversary q hq parameter
        hparameter ftsSecret hfts)

set_option maxRecDepth 100000 in
theorem chronologicalCleanRetainedRun_isProbeBound
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    (chronologicalCleanRetainedRun adversary parameter ftsSecret).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
  unfold chronologicalCleanRetainedRun
  have htail : ∀ rootResult ∈ support (maskedPublishedTreeRoot.run emptySplitHashCache),
      (do
        let restResult ← chronologicalCleanRetainedRest adversary parameter rootResult.1
          ftsSecret rootResult.2
        pure ((rootResult.1, restResult.1), restResult.2)).IsQueryBoundP
          (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q := by
    intro rootResult _hroot
    rcases rootResult with ⟨root, cache⟩
    let rest := chronologicalCleanRetainedRest adversary parameter root ftsSecret cache
    change ((fun result : RetainedRestResult × SplitHashCache =>
      ((root, result.1), result.2)) <$> rest).IsQueryBoundP
        (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) q
    rw [OracleComp.isQueryBoundP_map_iff]
    unfold rest chronologicalCleanRetainedRest
    exact maskedChronologicalRetainedGameRest_run_isProbeBound adversary parameter root ftsSecret q
      (hbound root) cache
  simpa only [Nat.zero_add] using OracleComp.isQueryBoundP_bind
    (n := 0) (m := q) (maskedPublishedTreeRoot_probeFree emptySplitHashCache) htail

theorem probEvent_sampledChronologicalCleanFinish_none_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    Pr[= none | sampledRunThenFinalizeClean
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) q
        (chronologicalCleanRetainedRun adversary parameter ftsSecret)] ≤
      (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  probEvent_sampledRunThenFinalizeClean_empty_none_le
    (chronologicalCleanRetainedRun adversary parameter ftsSecret) q
      (chronologicalCleanRetainedRun_isProbeBound adversary parameter ftsSecret q hbound)

noncomputable def sampledCanonicalDeferredFinishIsNone
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool := do
  let table ← sampleOtsHashTable
  let result ← canonicalDeferredRetainedRunAfterFtsSecrets adversary parameter table
    ftsSecret fuel
  finishResolvedRunIsNone result

theorem probEvent_finishResolvedRun_none_eq_isNone
    (run : ProbComp (Option (ResolvedRunResult α))) :
    Pr[= none | run >>= finishResolvedRun] =
      Pr[= true | run >>= finishResolvedRunIsNone] := by
  have hrun : run >>= finishResolvedRunIsNone =
      Option.isNone <$> (run >>= finishResolvedRun) := by
    unfold finishResolvedRunIsNone
    rw [map_bind]
  rw [hrun, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map]
  apply OracleComp.probEvent_congr' (fun result _ => by cases result <;> simp) rfl

set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_canonicalDeferred
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      Pr[= true |
        sampledCanonicalDeferredFinishIsNone adversary parameter ftsSecret fuel] := by
  unfold sampledActualRetainedOtsHashTable sampledCanonicalDeferredFinishIsNone
    sampleOtsHashTable
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_bind_of_forall_le
  intro table _htable
  calc
    _ ≤ Pr[= none |
        canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret
          fuel >>= finishResolvedRun] := by
      simpa [probEvent_map, Function.comp_def] using
        probEvent_winningRetainedVerifyProbe_le_canonicalFinishedResolvedRun_none adversary
          parameter table ftsSecret fuel
    _ = Pr[= true |
        canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret
          fuel >>= finishResolvedRunIsNone] :=
      probEvent_finishResolvedRun_none_eq_isNone _
    _ = Pr[= true |
        canonicalDeferredRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel >>=
          finishResolvedRunIsNone] :=
      prob_canonicalChronologicalRetainedFinishIsNone_eq_deferred adversary parameter table
        ftsSecret fuel
    _ = Pr[fun failed : Bool => failed = true |
        canonicalDeferredRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel >>=
          finishResolvedRunIsNone] := by
      rw [probEvent_eq_eq_probOutput]

set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_of_fixed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (bound : ℝ≥0∞)
    (hfixed : ∀ table : OtsSecretIndex → HashOutput,
      Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret
          (extendStartTable table)] ≤ bound) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤ bound := by
  unfold sampledActualRetainedOtsHashTable
  apply probEvent_bind_le_of_forall_le
  intro table _htable
  simpa [probEvent_map, Function.comp_def] using hfixed table

set_option linter.constructorNameAsVariable false in
theorem probEvent_sampledActualRetainedOtsSecrets_verifyProbe_le_of_fixed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (bound : ℝ≥0∞)
    (hfixed : ∀ table : OtsSecretIndex → HashOutput,
      Pr[WinningRetainedVerifyProbeWitness parameter (extendStartTable table) ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret
          (extendStartTable table)] ≤ bound) :
    Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
        ftsSecret result.2 |
      sampledActualRetainedOtsSecrets adversary parameter ftsSecret] ≤ bound := by
  rw [← probEvent_sampledWinningRetainedVerifyProbe_eq_secrets adversary parameter ftsSecret]
  exact probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_of_fixed adversary parameter
    ftsSecret bound hfixed

noncomputable def sampledViewedOtsSecrets (adversary : Adversary)
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((Layer → TreeIndex → LeafIndex → ChainIndex → Digest) ×
      ((Digest × Forgery × Bool) × ViewedFullTraceState)) := do
  let otsSecret ← sampleOtsSecrets
  let result ← gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  pure (otsSecret, result)

theorem probEvent_cleanFresh_le_verifyProbeAfterOtsSecret
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[cleanFreshEvent parameter otsSecret ftsSecret |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      Pr[WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret |
        actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret] := by
  let table := tableOfOtsSecret otsSecret
  calc
    _ ≤ Pr[WinningRetainedFreshLayerOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      simpa [table, tableOtsSecret_tableOfOtsSecret] using
        probEvent_cleanFresh_le_actualRetained adversary parameter table ftsSecret
    _ ≤ Pr[WinningRetainedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] :=
      probEvent_winningRetainedFresh_le_verifyProbe adversary parameter table ftsSecret
    _ = _ := by
      rw [actualRetainedGameAfterTable_eq_afterOtsSecret]
      simp only [table, tableOtsSecret_tableOfOtsSecret]
      rfl

theorem probEvent_cleanBackward_le_verifyProbeAfterOtsSecret
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[cleanBackwardEvent parameter otsSecret ftsSecret |
        gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      Pr[WinningRetainedVerifyProbeAfterOtsSecret parameter otsSecret ftsSecret |
        actualRetainedGameAfterOtsSecret adversary parameter ftsSecret otsSecret] := by
  let table := tableOfOtsSecret otsSecret
  calc
    _ ≤ Pr[WinningRetainedBackwardChainOpeningWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] := by
      simpa [table, tableOtsSecret_tableOfOtsSecret] using
        probEvent_cleanBackward_le_actualRetained adversary parameter table ftsSecret
    _ ≤ Pr[WinningRetainedVerifyProbeWitness parameter table ftsSecret |
        actualRetainedGameAfterTable adversary parameter ftsSecret table] :=
      probEvent_winningRetainedBackward_le_verifyProbe adversary parameter table ftsSecret
    _ = _ := by
      rw [actualRetainedGameAfterTable_eq_afterOtsSecret]
      simp only [table, tableOtsSecret_tableOfOtsSecret]
      rfl

theorem probEvent_sampledViewedOtsSecrets_cleanFresh_le_verifyProbe
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[fun result => cleanFreshEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] ≤
      Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] := by
  unfold sampledViewedOtsSecrets sampledActualRetainedOtsSecrets
  apply probEvent_bind_le_bind_of_forall_le
  intro otsSecret _hots
  simpa [probEvent_map, Function.comp_def] using
    probEvent_cleanFresh_le_verifyProbeAfterOtsSecret adversary parameter otsSecret ftsSecret

theorem probEvent_sampledViewedOtsSecrets_cleanBackward_le_verifyProbe
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    Pr[fun result => cleanBackwardEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] ≤
      Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] := by
  unfold sampledViewedOtsSecrets sampledActualRetainedOtsSecrets
  apply probEvent_bind_le_bind_of_forall_le
  intro otsSecret _hots
  simpa [probEvent_map, Function.comp_def] using
    probEvent_cleanBackward_le_verifyProbeAfterOtsSecret adversary parameter otsSecret ftsSecret

noncomputable def sampledViewedGameFtsFirst (adversary : Adversary) :
    ProbComp SampledViewedResult := do
  let parameter ← sampleParameter
  let ftsSecret ← sampleFtsSecrets
  let result ← sampledViewedOtsSecrets adversary parameter ftsSecret
  pure ⟨⟨parameter, result.1, ftsSecret⟩, result.2⟩

set_option maxRecDepth 100000 in
theorem evalDist_sampledViewedGame_eq_ftsFirst (adversary : Adversary) :
    𝒟[sampledViewedGame adversary] = 𝒟[sampledViewedGameFtsFirst adversary] := by
  unfold sampledViewedGame sampleSecrets sampledViewedGameFtsFirst sampledViewedOtsSecrets
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  exact OracleComp.DeferredSampling.evalDist_bind_comm sampleOtsSecrets sampleFtsSecrets
    (fun otsSecret ftsSecret => do
      let result ← gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
      pure (⟨⟨parameter, otsSecret, ftsSecret⟩, result⟩ : SampledViewedResult))

theorem probEvent_sampledViewedGame_cleanFresh_le_of_sampled
    (adversary : Adversary) (bound : ℝ≥0∞)
    (hsampled : ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[fun result => WinningRetainedVerifyProbeWitness parameter
            (extendStartTable result.1) ftsSecret result.2 |
          sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤ bound) :
    Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] ≤ bound := by
  have hrewrite :
      Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] =
        Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGameFtsFirst adversary] :=
    OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_sampledViewedGame_eq_ftsFirst adversary)
  rw [hrewrite]
  unfold sampledViewedGameFtsFirst
  apply probEvent_bind_le_of_forall_le
  intro parameter hparameter
  apply probEvent_bind_le_of_forall_le
  intro ftsSecret hfts
  calc
    _ = Pr[fun result => cleanFreshEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] := by
      change Pr[SampledViewedEvent cleanFreshEvent |
          (fun result =>
            (⟨⟨parameter, result.1, ftsSecret⟩, result.2⟩ : SampledViewedResult)) <$>
            sampledViewedOtsSecrets adversary parameter ftsSecret] = _
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] :=
      probEvent_sampledViewedOtsSecrets_cleanFresh_le_verifyProbe adversary parameter ftsSecret
    _ = Pr[fun result => WinningRetainedVerifyProbeWitness parameter
          (extendStartTable result.1) ftsSecret result.2 |
        sampledActualRetainedOtsHashTable adversary parameter ftsSecret] :=
      (probEvent_sampledWinningRetainedVerifyProbe_eq_secrets adversary parameter ftsSecret).symm
    _ ≤ bound := hsampled parameter hparameter ftsSecret hfts

theorem probEvent_sampledViewedGame_cleanBackward_le_of_sampled
    (adversary : Adversary) (bound : ℝ≥0∞)
    (hsampled : ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[fun result => WinningRetainedVerifyProbeWitness parameter
            (extendStartTable result.1) ftsSecret result.2 |
          sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤ bound) :
    Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] ≤ bound := by
  have hrewrite :
      Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] =
        Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGameFtsFirst adversary] :=
    OracleComp.probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_sampledViewedGame_eq_ftsFirst adversary)
  rw [hrewrite]
  unfold sampledViewedGameFtsFirst
  apply probEvent_bind_le_of_forall_le
  intro parameter hparameter
  apply probEvent_bind_le_of_forall_le
  intro ftsSecret hfts
  calc
    _ = Pr[fun result => cleanBackwardEvent parameter result.1 ftsSecret result.2 |
        sampledViewedOtsSecrets adversary parameter ftsSecret] := by
      change Pr[SampledViewedEvent cleanBackwardEvent |
          (fun result =>
            (⟨⟨parameter, result.1, ftsSecret⟩, result.2⟩ : SampledViewedResult)) <$>
            sampledViewedOtsSecrets adversary parameter ftsSecret] = _
      rw [probEvent_map]
      rfl
    _ ≤ Pr[fun result => WinningRetainedVerifyProbeAfterOtsSecret parameter result.1
          ftsSecret result.2 |
        sampledActualRetainedOtsSecrets adversary parameter ftsSecret] :=
      probEvent_sampledViewedOtsSecrets_cleanBackward_le_verifyProbe adversary parameter ftsSecret
    _ = Pr[fun result => WinningRetainedVerifyProbeWitness parameter
          (extendStartTable result.1) ftsSecret result.2 |
        sampledActualRetainedOtsHashTable adversary parameter ftsSecret] :=
      (probEvent_sampledWinningRetainedVerifyProbe_eq_secrets adversary parameter ftsSecret).symm
    _ ≤ bound := hsampled parameter hparameter ftsSecret hfts

theorem security_of_sampledWinningRetainedVerifyProbe_le
    (hprobe : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[fun result => WinningRetainedVerifyProbeWitness parameter
            (extendStartTable result.1) ftsSecret result.2 |
          sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
          (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    SphincsSecurityStatement := by
  apply security_of_sampled_hiddenOpeningRisk_le
  intro q hqPos adversary hq hqMax
  let bound := (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  have hsampled : ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[fun result => WinningRetainedVerifyProbeWitness parameter
            (extendStartTable result.1) ftsSecret result.2 |
          sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤ bound := by
    intro parameter hparameter ftsSecret hfts
    exact hprobe q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts
  have hfresh :
      Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] ≤ bound :=
    probEvent_sampledViewedGame_cleanFresh_le_of_sampled adversary bound hsampled
  have hbackward :
      Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] ≤ bound :=
    probEvent_sampledViewedGame_cleanBackward_le_of_sampled adversary bound hsampled
  have huncovered :
      Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤ bound :=
    FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le adversary q hq
  rw [sampledHiddenOpeningRisk]
  calc
    _ ≤ bound + (bound + bound) := add_le_add hfresh (add_le_add hbackward huncovered)
    _ = ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      simp only [bound]
      push_cast
      ring
    _ ≤ ((19 * q : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      omega

end SphincsSecurity.Concrete.OtsProbeSimulation
