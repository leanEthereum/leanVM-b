import SphincsSecurity.Proof.SigningReplay

/-!
# Successful signer executions

A successful signer invocation exposes its chosen index and leaf vector, its honest few-time
opening, and one successful honest one-time signing computation at every layer.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev LayerPart :=
  Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)

theorem otsSignFrom_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest)
    (message : Digest) (attempts counter : Nat) (resultCounter : Counter)
    (values : ChainIndex → Digest)
    (hsign : evalWithAnswerFn f
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter)
        = some (resultCounter, values)) :
    ∃ codeword : Encoding,
      evalWithAnswerFn f (encode parameter lay tree leafIdx message resultCounter)
          = some codeword
        ∧ ∀ chainIdx, values chainIdx =
          honestChain f parameter lay tree leafIdx chainIdx (secret chainIdx)
            (codeword chainIdx).val := by
  induction attempts generalizing counter with
  | zero => simp [otsSignFrom] at hsign
  | succ attempts ih =>
      rw [otsSignFrom, evalWithAnswerFn_bind] at hsign
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leafIdx message (BitVec.ofNat counterBits counter)) with
      | none =>
          simp only [hencode] at hsign
          exact ih (counter + 1) hsign
      | some codeword =>
          simp only [hencode, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
            evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hsign
          obtain ⟨hcounter, hvalues⟩ := hsign
          subst resultCounter
          refine ⟨codeword, hencode, ?_⟩
          intro chainIdx
          rw [← congrFun hvalues chainIdx]
          rfl

def SuccessfulLayerRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (lay : Layer) (part : LayerPart) : Prop :=
  ∃ codeword : Encoding,
    evalWithAnswerFn f
        (encode secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f (layerMessage secretKey index lay)) part.1)
      = some codeword
      ∧ (∀ chainIdx, part.2.1 chainIdx =
        honestChain f secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          chainIdx (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)
          (codeword chainIdx).val)
      ∧ (∀ level, part.2.2 level = if level.val < layerHeight lay then
        honestNode f secretKey.parameter lay (treeIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay)) level.val
          (Nat.xor ((leafIndexAt index lay).val / 2 ^ level.val) 1)
        else 0)
      ∧ evalWithAnswerFn f
        (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
          (evalWithAnswerFn f (layerMessage secretKey index lay))) = some (part.1, part.2.1)
      ∧ CachedRun cache f (layerMessage secretKey index lay)
      ∧ CachedRun cache f
        (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
          (evalWithAnswerFn f (layerMessage secretKey index lay)))
      ∧ CachedRun cache f
        (treePath secretKey.parameter lay (treeIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay))

theorem successfulLayerRun_of_eval (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (lay : Layer) (part : LayerPart)
    (heval : evalWithAnswerFn f (signLayer secretKey index lay) = some part)
    (hrun : CachedRun cache f (signLayer secretKey index lay)) :
    SuccessfulLayerRun f cache secretKey index lay part := by
  rw [signLayer, evalWithAnswerFn_bind] at heval
  rw [evalWithAnswerFn_bind] at heval
  rw [signLayer] at hrun
  have hmessageRun : CachedRun cache f (layerMessage secretKey index lay) := hrun.bind_left
  have hrestRun := hrun.bind_right
  cases hots : evalWithAnswerFn f
      (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
        (evalWithAnswerFn f (layerMessage secretKey index lay))) with
  | none =>
      simp only [hots, evalWithAnswerFn_pure] at heval
      cases heval
  | some signed =>
      obtain ⟨counter, values⟩ := signed
      have hotsRun := hrestRun.bind_left
      have hafterOts := hrestRun.bind_right
      rw [hots] at hafterOts
      have hpathRun := hafterOts.bind_left
      simp only [hots, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at heval
      have hcounter : counter = part.1 := congrArg Prod.fst heval
      have hvalues : values = part.2.1 := congrArg (fun value => value.2.1) heval
      have hpath : evalWithAnswerFn f
          (treePath secretKey.parameter lay (treeIndexAt index lay)
            (secretKey.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay))
          = part.2.2 := congrArg (fun value => value.2.2) heval
      obtain ⟨codeword, hencode, hchains⟩ := otsSignFrom_some f secretKey.parameter lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
        (evalWithAnswerFn f (layerMessage secretKey index lay)) encodingAttemptLimit 0 counter
        values (by simpa only [otsSign] using hots)
      refine ⟨codeword, ?_, ?_, ?_, ?_, hmessageRun, hotsRun, hpathRun⟩
      · rwa [← hcounter]
      · intro chainIdx
        rw [← hvalues]
        exact hchains chainIdx
      · intro level
        rw [← hpath]
        simp only [treePath, evalWithAnswerFn_sequenceFin]
        split <;> rfl
      · simpa only [hcounter, hvalues] using hots

theorem traverseOption_eq_some_apply {alpha : Type} {n : Nat}
    (family : Fin n → Option alpha) (values : Fin n → alpha)
    (h : traverseOption family = some values) (index : Fin n) :
    family index = some (values index) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      cases hhead : family 0 with
      | none => simp [traverseOption, hhead] at h
      | some head =>
          cases htail : traverseOption (fun index : Fin n => family index.succ) with
          | none => simp [traverseOption, hhead, htail] at h
          | some tail =>
              have hvalues : Fin.cases head tail = values := by
                simpa [traverseOption, hhead, htail] using h
              cases index using Fin.cases with
              | zero =>
                  have := congrFun hvalues 0
                  simpa [hhead] using congrArg some this
              | succ index =>
                  have hfamily := ih (fun index : Fin n => family index.succ) tail htail index
                  have hvalue := congrFun hvalues index.succ
                  rw [← hvalue]
                  exact hfamily

def SuccessfulDigestRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) : Prop :=
  randomness ∈ support sampleRandomness
    ∧ evalWithAnswerFn f (signAttempt secretKey message randomness) = some (index, leaves)
    ∧ CachedRun cache f (signAttempt secretKey message randomness)

theorem SuccessfulDigestRun.extract {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {randomness : Randomness} {index : Index}
    {leaves : DigestTree → FtsLeaf}
    (hrun : SuccessfulDigestRun f cache secretKey message randomness index leaves) :
    randomness ∈ support sampleRandomness
      ∧ ∃ digest : MessageDigest,
        evalWithAnswerFn f
            (messageDigest secretKey.parameter secretKey.root message randomness) = digest
          ∧ Admissible digest
          ∧ index = digestIndex digest
          ∧ leaves = digestLeaves digest
          ∧ CachedRun cache f
            (messageDigest secretKey.parameter secretKey.root message randomness) := by
  refine ⟨hrun.1, ?_⟩
  have heval := hrun.2.1
  simp only [signAttempt, evalWithAnswerFn_bind] at heval
  let digest := evalWithAnswerFn f
    (messageDigest secretKey.parameter secretKey.root message randomness)
  by_cases hadmissible : Admissible digest
  · simp only [show Admissible (evalWithAnswerFn f
        (messageDigest secretKey.parameter secretKey.root message randomness)) from hadmissible,
      if_true, evalWithAnswerFn_pure] at heval
    have hresult : (digestIndex digest, digestLeaves digest) = (index, leaves) :=
      Option.some.inj heval
    have hfields := Prod.mk.inj hresult
    refine ⟨digest, rfl, hadmissible, hfields.1.symm, hfields.2.symm, ?_⟩
    exact hrun.2.2.bind_left
  · simp only [show ¬ Admissible (evalWithAnswerFn f
        (messageDigest secretKey.parameter secretKey.root message randomness)) from hadmissible,
      if_false, evalWithAnswerFn_pure] at heval
    simp at heval

theorem successfulDigestLoop_of_mem_support (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (message : Message) (attempts : Nat) (randomness : Randomness)
    (index : Index) (leaves : DigestTree → FtsLeaf)
    (beforeCache afterCache finalCache : QueryCache HashSpec)
    (hmem : (some (randomness, index, leaves), afterCache) ∈ support
      ((simulateQ (replayRomImpl f) (signDigestLoop attempts secretKey message)).run beforeCache))
    (hleFinal : afterCache ≤ finalCache) (hf : finalCache.AgreesWithFn f) :
    SuccessfulDigestRun f finalCache secretKey message randomness index leaves := by
  induction attempts generalizing beforeCache afterCache randomness index leaves with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      cases hmem.1
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨sampledRandomness, sampleCache⟩, hsample, hrest⟩ := hmem
      have hsample' : (sampledRandomness, sampleCache) ∈ support
          ((simulateQ (unifFwdImpl HashSpec) sampleRandomness).run beforeCache) := by
        simpa only [replayRomImpl, QueryImpl.simulateQ_add_liftM_left] using hsample
      rw [unifFwdImpl.simulateQ_run, support_map] at hsample'
      obtain ⟨sampledRandomness', hsampled, heq⟩ := hsample'
      obtain ⟨rfl, rfl⟩ := heq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      cases attempt with
      | none =>
          exact ih (randomness := randomness) (index := index) (leaves := leaves)
            (beforeCache := attemptCache) (afterCache := afterCache) hfinish hleFinal
      | some selected =>
          obtain ⟨selectedIndex, selectedLeaves⟩ := selected
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hfinish
          obtain ⟨hresult, hcache⟩ := hfinish
          obtain ⟨rfl, rfl, rfl⟩ := hresult
          have hleAttempt : attemptCache ≤ finalCache := by
            rw [← hcache]
            exact hleFinal
          have hattempt' : (some (index, leaves), attemptCache) ∈ support
              ((simulateQ (replayHashImpl f)
                (signAttempt secretKey message randomness)).run beforeCache) := by
            simpa only [simulateQ_replayRom_liftM] using hattempt
          have hfAttempt : attemptCache.AgreesWithFn f :=
            fun _ _ hcached => hf (hleAttempt hcached)
          obtain ⟨_, heval, hcached⟩ := replayHash_of_mem_support f
            (signAttempt secretKey message randomness) beforeCache (some (index, leaves))
            attemptCache hattempt' hfAttempt
          exact ⟨hsampled, heval, hcached.mono hleAttempt⟩

def SuccessfulSignRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (signature : Signature) : Prop :=
  ∃ (index : Index) (leaves : DigestTree → FtsLeaf) (parts : Layer → LayerPart),
    SuccessfulDigestRun f cache secretKey message signature.randomness index leaves
      ∧ signature.ftsSecret =
        (fun tree => secretKey.ftsSecret index tree (leaves (ftsIndexOf tree)))
      ∧ signature.ftsPath =
        evalWithAnswerFn f (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index))
      ∧ signature.counter = (fun lay => (parts lay).1)
      ∧ signature.chainValue = (fun lay => (parts lay).2.1)
      ∧ signature.authPath = flattenPaths (fun lay => (parts lay).2.2)
      ∧ CachedRun cache f
        (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index))
      ∧ (∀ lay, evalWithAnswerFn f (signLayer secretKey index lay) = some (parts lay))
      ∧ ∀ lay, CachedRun cache f (signLayer secretKey index lay)

theorem successfulSignRun_of_mem_support (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (message : Message) (signature : Signature)
    (beforeCache afterCache finalCache : QueryCache HashSpec)
    (hmem : (some signature, afterCache) ∈ support
      ((simulateQ (replayRomImpl f) (sign secretKey message)).run beforeCache))
    (hleFinal : afterCache ≤ finalCache) (hf : finalCache.AgreesWithFn f) :
    SuccessfulSignRun f finalCache secretKey message signature := by
  rw [sign_eq, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hrest⟩ := hmem
  cases loopResult with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hrest
      cases hrest.1
  | some data =>
      obtain ⟨randomness, index, leaves⟩ := data
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨ftsPath, ftsCache⟩, hfts, hlayersRest⟩ := hrest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hlayersRest
      obtain ⟨⟨layers, layersCache⟩, hlayers, hfinal⟩ := hlayersRest
      cases hparts : traverseOption layers with
      | none =>
          simp only [hparts, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hfinal
          cases hfinal.1
      | some parts =>
          simp only [hparts, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hfinal
          obtain ⟨hsignature, hcache⟩ := hfinal
          subst signature
          subst afterCache
          have hfts' : (ftsPath, ftsCache) ∈ support
              ((simulateQ (replayHashImpl f)
                (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index))).run
                loopCache) := by
            simpa only [simulateQ_replayRom_liftM] using hfts
          have hlayers' : (layers, layersCache) ∈ support
              ((simulateQ (replayHashImpl f)
                (sequenceFin (fun lay => signLayer secretKey index lay))).run ftsCache) := by
            simpa only [simulateQ_replayRom_liftM] using hlayers
          have hftsLe : ftsCache ≤ layersCache :=
            simulateQ_replayRom_cache_le f
              (liftM (sequenceFin (fun lay => signLayer secretKey index lay)) :
                OracleComp OracleWorld (Layer →
                  Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))))
              ftsCache _ hlayers
          have hfLayers : layersCache.AgreesWithFn f :=
            fun _ _ hcached => hf (hleFinal hcached)
          have hfFts : ftsCache.AgreesWithFn f :=
            fun _ _ hcached => hfLayers (hftsLe hcached)
          obtain ⟨_, hftsEval, hftsCached⟩ :=
            replayHash_of_mem_support f
              (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index))
              loopCache ftsPath ftsCache hfts' hfFts
          obtain ⟨_, hlayersEval, hlayersCached⟩ :=
            replayHash_of_mem_support f
              (sequenceFin (fun lay => signLayer secretKey index lay))
              ftsCache layers layersCache hlayers' hfLayers
          have hpartsAt : ∀ lay, layers lay = some (parts lay) := by
            intro lay
            exact traverseOption_eq_some_apply layers parts hparts lay
          have hftsStartLe : loopCache ≤ ftsCache :=
            simulateQ_replayRom_cache_le f
              (liftM (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index)) :
                OracleComp OracleWorld (FtsTree → Fin ftsTreeHeight → Digest))
              loopCache _ hfts
          have hloopFinal : loopCache ≤ finalCache := hftsStartLe.trans (hftsLe.trans hleFinal)
          have hdigest := successfulDigestLoop_of_mem_support f secretKey message
            digestAttemptLimit randomness index leaves beforeCache loopCache finalCache hloop
            hloopFinal hf
          refine ⟨index, leaves, parts, hdigest, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
          · rw [← hftsEval]
          · exact (hftsCached.mono hftsLe).mono hleFinal
          · intro lay
            rw [← hpartsAt lay, ← hlayersEval]
            exact (congrFun
              (evalWithAnswerFn_sequenceFin f (fun lay => signLayer secretKey index lay)) lay).symm
          · intro lay
            exact (hlayersCached.sequenceFin_component
              (fun lay => signLayer secretKey index lay) lay).mono hleFinal

theorem successfulSignRun_of_signing_entry (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initialCache : QueryCache HashSpec) (value : alpha) (signingLog : QueryLog SigningSpec)
    (adversaryCache finalCache : QueryCache HashSpec)
    (hmem : ((value, signingLog), adversaryCache) ∈ support
      ((simulateQ romImpl
        ((simulateQ (forwardOracles + signingOracle scheme secretKey)
          computation).run)).run initialCache))
    (hle : adversaryCache ≤ finalCache) (hf : finalCache.AgreesWithFn f)
    (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
    (hresponse : entry.2 = some signature) (hentry : entry ∈ signingLog) :
    SuccessfulSignRun f finalCache secretKey entry.1 signature := by
  obtain ⟨beforeCache, afterCache, hsign, hafter⟩ := signing_entry_of_mem_support f
    secretKey computation initialCache value signingLog adversaryCache finalCache hmem hle hf
    entry hentry
  have hsign' : (some signature, afterCache) ∈ support
      ((simulateQ (replayRomImpl f) (scheme.sign secretKey entry.1)).run beforeCache) := by
    rwa [← hresponse]
  exact successfulSignRun_of_mem_support f secretKey entry.1 signature beforeCache afterCache
    finalCache (by simpa only [scheme] using hsign') hafter hf

theorem SuccessfulSignRun.layer {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f cache secretKey message signature) (lay : Layer) :
    ∃ (index : Index) (parts : Layer → LayerPart),
      signature.counter = (fun lay => (parts lay).1)
      ∧ signature.chainValue = (fun lay => (parts lay).2.1)
      ∧ signature.authPath = flattenPaths (fun lay => (parts lay).2.2)
      ∧ SuccessfulLayerRun f cache secretKey index lay (parts lay) := by
  obtain ⟨index, leaves, parts, _, _, _, hcounter, hvalues, hpath, _, heval, hcached⟩ := hrun
  exact ⟨index, parts, hcounter, hvalues, hpath,
    successfulLayerRun_of_eval f cache secretKey index lay (parts lay) (heval lay) (hcached lay)⟩

theorem SuccessfulSignRun.indexed {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {signature : Signature}
    (hrun : SuccessfulSignRun f cache secretKey message signature) :
    ∃ (index : Index) (leaves : DigestTree → FtsLeaf) (parts : Layer → LayerPart),
      SuccessfulDigestRun f cache secretKey message signature.randomness index leaves
        ∧ signature.ftsSecret =
          (fun tree => secretKey.ftsSecret index tree (leaves (ftsIndexOf tree)))
        ∧ signature.ftsPath = evalWithAnswerFn f
          (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index))
        ∧ signature.counter = (fun lay => (parts lay).1)
        ∧ signature.chainValue = (fun lay => (parts lay).2.1)
        ∧ signature.authPath = flattenPaths (fun lay => (parts lay).2.2)
        ∧ CachedRun cache f
          (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index))
        ∧ ∀ lay, SuccessfulLayerRun f cache secretKey index lay (parts lay) := by
  obtain ⟨index, leaves, parts, hdigest, hsecret, hpath, hcounter, hvalues, hauth, hfts, heval,
    hcached⟩ := hrun
  exact ⟨index, leaves, parts, hdigest, hsecret, hpath, hcounter, hvalues, hauth, hfts,
    fun lay => successfulLayerRun_of_eval f cache secretKey index lay (parts lay)
      (heval lay) (hcached lay)⟩

theorem SuccessfulLayerRun.message_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {index : Index} {lay : Layer}
    {part : LayerPart} (hrun : SuccessfulLayerRun f cache secretKey index lay part) :
    CachedRun cache f (layerMessage secretKey index lay) := by
  obtain ⟨_, _, _, _, _, hmessage, _, _⟩ := hrun
  exact hmessage

theorem SuccessfulLayerRun.otsSign_eval_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {index : Index} {lay : Layer}
    {part : LayerPart} (hrun : SuccessfulLayerRun f cache secretKey index lay part) :
    evalWithAnswerFn f
        (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
          (evalWithAnswerFn f (layerMessage secretKey index lay))) = some (part.1, part.2.1)
      ∧ CachedRun cache f
        (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
          (evalWithAnswerFn f (layerMessage secretKey index lay))) := by
  obtain ⟨_, _, _, _, heval, _, hcached, _⟩ := hrun
  exact ⟨heval, hcached⟩

theorem SuccessfulSignRun.honest_openings {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature) :
    ∃ index, ∀ lay, HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
      (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
      (signature.chainValue lay) (signaturePath signature lay) := by
  obtain ⟨index, _, parts, _, _, _, hcounter, hvalues, hauth, _, hlayers⟩ := hrun.indexed
  refine ⟨index, fun lay => ?_⟩
  obtain ⟨codeword, hencode, hchains, hpath, _, _, _, _⟩ := hlayers lay
  refine ⟨codeword, ?_, ?_, ?_⟩
  · simpa only [congrFun hcounter lay] using hencode
  · intro chainIdx
    rw [congrFun hvalues lay]
    exact hchains chainIdx
  · intro level hlevel
    let levelFin : Fin maxLayerHeight :=
      ⟨level, lt_of_lt_of_le hlevel (layerHeight_le lay)⟩
    rw [show level = levelFin.val from rfl]
    rw [signaturePath_flattenPaths signature (fun lay => (parts lay).2.2) hauth lay levelFin
      hlevel]
    have hlevelFin : levelFin.val < layerHeight lay := hlevel
    simpa only [if_pos hlevelFin] using hpath levelFin

theorem SuccessfulSignRun.honest_layer_at {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    (lay : Layer) :
    ∃ index,
      CachedRun cache f (layerMessage secretKey index lay)
        ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
          (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
          (signature.chainValue lay) (signaturePath signature lay) := by
  obtain ⟨index, _, parts, _, _, _, hcounter, hvalues, hauth, _, hlayers⟩ := hrun.indexed
  obtain ⟨codeword, hencode, hchains, hpath, _, hmessage, _, _⟩ := hlayers lay
  refine ⟨index, hmessage, codeword, ?_, ?_, ?_⟩
  · simpa only [congrFun hcounter lay] using hencode
  · intro chainIdx
    rw [congrFun hvalues lay]
    exact hchains chainIdx
  · intro level hlevel
    let levelFin : Fin maxLayerHeight :=
      ⟨level, lt_of_lt_of_le hlevel (layerHeight_le lay)⟩
    rw [show level = levelFin.val from rfl]
    rw [signaturePath_flattenPaths signature (fun lay => (parts lay).2.2) hauth lay levelFin
      hlevel]
    have hlevelFin : levelFin.val < layerHeight lay := hlevel
    simpa only [if_pos hlevelFin] using hpath levelFin

theorem SuccessfulSignRun.honest_layer_at_of_digest {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hdigest : SuccessfulDigestRun f cache secretKey message signature.randomness index leaves)
    (lay : Layer) :
    CachedRun cache f (layerMessage secretKey index lay)
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay) := by
  obtain ⟨runIndex, runLeaves, parts, hrunDigest, _, _, hcounter, hvalues, hauth, _, hlayers⟩ :=
    hrun.indexed
  obtain ⟨_, digest, hrunEval, _, hrunIndex, _, _⟩ := hrunDigest.extract
  obtain ⟨_, digest', hdigestEval, _, hdigestIndex, _, _⟩ := hdigest.extract
  have hdigests : digest = digest' := by rw [← hrunEval, ← hdigestEval]
  have hindex : runIndex = index := by rw [hrunIndex, hdigestIndex, hdigests]
  obtain ⟨codeword, hencode, hchains, hpath, _, hmessage, _, _⟩ := hlayers lay
  refine ⟨?_, codeword, ?_, ?_, ?_⟩
  · simpa only [hindex] using hmessage
  · simpa only [hindex, congrFun hcounter lay] using hencode
  · intro chainIdx
    rw [congrFun hvalues lay]
    simpa only [hindex] using hchains chainIdx
  · intro level hlevel
    let levelFin : Fin maxLayerHeight :=
      ⟨level, lt_of_lt_of_le hlevel (layerHeight_le lay)⟩
    rw [show level = levelFin.val from rfl]
    rw [signaturePath_flattenPaths signature (fun lay => (parts lay).2.2) hauth lay levelFin
      hlevel]
    have hlevelFin : levelFin.val < layerHeight lay := hlevel
    simpa only [hindex, if_pos hlevelFin] using hpath levelFin

theorem SuccessfulSignRun.signature_part_of_digest {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hdigest : SuccessfulDigestRun f cache secretKey message signature.randomness index leaves)
    (lay : Layer) :
    ∃ part : LayerPart,
      evalWithAnswerFn f (signLayer secretKey index lay) = some part
        ∧ signature.counter lay = part.1
        ∧ signature.chainValue lay = part.2.1 := by
  obtain ⟨runIndex, _, parts, hrunDigest, _, _, hcounter, hvalues, _, _, heval, _⟩ := hrun
  obtain ⟨_, digest, hrunEval, _, hrunIndex, _, _⟩ := hrunDigest.extract
  obtain ⟨_, digest', hdigestEval, _, hdigestIndex, _, _⟩ := hdigest.extract
  have hdigests : digest = digest' := by rw [← hrunEval, ← hdigestEval]
  have hindex : runIndex = index := by rw [hrunIndex, hdigestIndex, hdigests]
  refine ⟨parts lay, ?_, congrFun hcounter lay, congrFun hvalues lay⟩
  simpa only [hindex] using heval lay

theorem SuccessfulSignRun.layerRun_of_digest {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hdigest : SuccessfulDigestRun f cache secretKey message signature.randomness index leaves)
    (lay : Layer) :
    ∃ part : LayerPart, signature.counter lay = part.1
      ∧ signature.chainValue lay = part.2.1
      ∧ SuccessfulLayerRun f cache secretKey index lay part := by
  obtain ⟨runIndex, _, parts, hrunDigest, _, _, hcounter, hvalues, _, _, hlayers⟩ := hrun.indexed
  obtain ⟨_, digest, hrunEval, _, hrunIndex, _, _⟩ := hrunDigest.extract
  obtain ⟨_, digest', hdigestEval, _, hdigestIndex, _, _⟩ := hdigest.extract
  have hdigests : digest = digest' := by rw [← hrunEval, ← hdigestEval]
  have hindex : runIndex = index := by rw [hrunIndex, hdigestIndex, hdigests]
  refine ⟨parts lay, congrFun hcounter lay, congrFun hvalues lay, ?_⟩
  simpa only [hindex] using hlayers lay

theorem SuccessfulSignRun.signLayer_cached_of_digest {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature)
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hdigest : SuccessfulDigestRun f cache secretKey message signature.randomness index leaves)
    (lay : Layer) : CachedRun cache f (signLayer secretKey index lay) := by
  obtain ⟨runIndex, _, _, hrunDigest, _, _, _, _, _, _, _, hcached⟩ := hrun
  obtain ⟨_, digest, hrunEval, _, hrunIndex, _, _⟩ := hrunDigest.extract
  obtain ⟨_, digest', hdigestEval, _, hdigestIndex, _, _⟩ := hdigest.extract
  have hdigests : digest = digest' := by rw [← hrunEval, ← hdigestEval]
  have hindex : runIndex = index := by rw [hrunIndex, hdigestIndex, hdigests]
  simpa only [hindex] using hcached lay

theorem SuccessfulSignRun.honest_fts_opening {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature) :
    ∃ (index : Index) (leaves : DigestTree → FtsLeaf),
      signature.ftsSecret =
          (fun tree => secretKey.ftsSecret index tree (leaves (ftsIndexOf tree)))
        ∧ signature.ftsPath = fun tree level =>
          honestFtsNode f secretKey.parameter index tree (secretKey.ftsSecret index tree)
            level.val (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1) := by
  obtain ⟨index, leaves, _, _, hsecret, hpath, _, _, _, _, _⟩ := hrun.indexed
  refine ⟨index, leaves, hsecret, hpath.trans ?_⟩
  funext tree level
  simp only [ftsOpen, evalWithAnswerFn_sequenceFin]
  rfl

def HonestFtsSignAt (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (signature : Signature) (index : Index)
    (leaves : DigestTree → FtsLeaf) : Prop :=
  SuccessfulDigestRun f cache secretKey message signature.randomness index leaves
    ∧ signature.ftsSecret =
      (fun tree => secretKey.ftsSecret index tree (leaves (ftsIndexOf tree)))
    ∧ signature.ftsPath = fun tree level =>
      honestFtsNode f secretKey.parameter index tree (secretKey.ftsSecret index tree)
        level.val (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

theorem SuccessfulSignRun.honest_fts_at {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hrun : SuccessfulSignRun f cache secretKey message signature) :
    ∃ index leaves, HonestFtsSignAt f cache secretKey message signature index leaves := by
  obtain ⟨index, leaves, _, hdigest, hsecret, hpath, _, _, _, _, _⟩ := hrun.indexed
  refine ⟨index, leaves, hdigest, hsecret, hpath.trans ?_⟩
  funext tree level
  simp only [ftsOpen, evalWithAnswerFn_sequenceFin]
  rfl

theorem SuccessfulSignRun.middle_root_settled {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hf : cache.AgreesWithFn f)
    (hrun : SuccessfulSignRun f cache secretKey message signature) :
    ∃ index, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (.node middleLayer (treeIndexAt index middleLayer)
        ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩) := by
  obtain ⟨index, _, _, _, _, _, _, _, _, _, hlayer⟩ := hrun.indexed
  have hcached := (hlayer topLayer).message_cached
  rw [layerMessage_of_lt secretKey index topLayer (by decide)] at hcached
  refine ⟨index, ?_⟩
  simpa only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl] using
    settled_treeRoot_of_cachedRun (ftsSecret := secretKey.ftsSecret) hf middleLayer
      (treeIndexAt index middleLayer) hcached

theorem SuccessfulSignRun.bottom_root_settled {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hf : cache.AgreesWithFn f)
    (hrun : SuccessfulSignRun f cache secretKey message signature) :
    ∃ index, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (.node bottomLayer (treeIndexAt index bottomLayer)
        ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩) := by
  obtain ⟨index, _, _, _, _, _, _, _, _, _, hlayer⟩ := hrun.indexed
  have hcached := (hlayer middleLayer).message_cached
  rw [layerMessage_of_lt secretKey index middleLayer (by decide)] at hcached
  refine ⟨index, ?_⟩
  simpa only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl] using
    settled_treeRoot_of_cachedRun (ftsSecret := secretKey.ftsSecret) hf bottomLayer
      (treeIndexAt index bottomLayer) hcached

theorem SuccessfulSignRun.fts_roots_settled {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hf : cache.AgreesWithFn f)
    (hrun : SuccessfulSignRun f cache secretKey message signature) :
    ∃ index, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (.ftsRoots index) := by
  obtain ⟨index, _, _, _, _, _, _, _, _, _, hlayer⟩ := hrun.indexed
  have hcached := (hlayer bottomLayer).message_cached
  rw [layerMessage_bottomLayer secretKey index] at hcached
  exact ⟨index, settled_ftsRoots_of_cachedRun (otsSecret := secretKey.otsSecret) hf index hcached⟩

theorem index_eq_of_bottom_position_eq {left right : Index}
    (htree : treeIndexAt left bottomLayer = treeIndexAt right bottomLayer)
    (hleaf : leafIndexAt left bottomLayer = leafIndexAt right bottomLayer) : left = right := by
  apply Fin.ext
  have htreeVal := congrArg Fin.val htree
  have hleafVal := congrArg Fin.val hleaf
  have habove : heightAbove bottomLayer = 19 := by decide
  have hheight : layerHeight bottomLayer = 7 := by decide
  have hleftTree : (treeIndexAt left bottomLayer).val = left.val / 128 := by
    rw [treeIndexAt_val, habove]
    norm_num [totalHeight]
  have hrightTree : (treeIndexAt right bottomLayer).val = right.val / 128 := by
    rw [treeIndexAt_val, habove]
    norm_num [totalHeight]
  have hleftLeaf : (leafIndexAt left bottomLayer).val = left.val % 128 := by
    rw [leafIndexAt_bottomLayer, hheight]
    norm_num
  have hrightLeaf : (leafIndexAt right bottomLayer).val = right.val % 128 := by
    rw [leafIndexAt_bottomLayer, hheight]
    norm_num
  rw [hleftTree, hrightTree] at htreeVal
  rw [hleftLeaf, hrightLeaf] at hleafVal
  omega

theorem layerMessage_eq_of_position_eq (secretKey : SecretKey) (left right : Index)
    (lay : Layer) (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    layerMessage (m := OracleComp HashSpec) secretKey left lay =
      layerMessage secretKey right lay := by
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  rcases hlayer with rfl | rfl | rfl
  · have hnext : treeIndexAt left middleLayer = treeIndexAt right middleLayer := by
      apply Fin.ext
      rw [layers_link_top left, layers_link_top right]
      rw [congrArg Fin.val htree, congrArg Fin.val hleaf]
    rw [layerMessage_of_lt secretKey left topLayer (by decide),
      layerMessage_of_lt secretKey right topLayer (by decide)]
    simp only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl, hnext]
  · have hnext : treeIndexAt left bottomLayer = treeIndexAt right bottomLayer := by
      apply Fin.ext
      rw [layers_link_middle left, layers_link_middle right]
      rw [congrArg Fin.val htree, congrArg Fin.val hleaf]
    rw [layerMessage_of_lt secretKey left middleLayer (by decide),
      layerMessage_of_lt secretKey right middleLayer (by decide)]
    simp only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl, hnext]
  · have hindex := index_eq_of_bottom_position_eq htree hleaf
    subst right
    rfl

theorem signLayer_eq_of_position_eq (secretKey : SecretKey) (left right : Index)
    (lay : Layer) (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    signLayer (m := OracleComp HashSpec) secretKey left lay =
      signLayer secretKey right lay := by
  simp only [signLayer]
  rw [htree, hleaf,
    layerMessage_eq_of_position_eq secretKey left right lay htree hleaf]

theorem successfulSignRun_layer_ots_eq_of_position_eq {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {leftMessage rightMessage : Message} {leftSignature rightSignature : Signature}
    (left : SuccessfulSignRun f cache secretKey leftMessage leftSignature)
    (right : SuccessfulSignRun f cache secretKey rightMessage rightSignature)
    {leftIndex rightIndex : Index}
    {leftLeaves rightLeaves : DigestTree → FtsLeaf}
    (leftDigest : SuccessfulDigestRun f cache secretKey leftMessage leftSignature.randomness
      leftIndex leftLeaves)
    (rightDigest : SuccessfulDigestRun f cache secretKey rightMessage rightSignature.randomness
      rightIndex rightLeaves)
    (lay : Layer) (htree : treeIndexAt leftIndex lay = treeIndexAt rightIndex lay)
    (hleaf : leafIndexAt leftIndex lay = leafIndexAt rightIndex lay) :
    leftSignature.counter lay = rightSignature.counter lay
      ∧ leftSignature.chainValue lay = rightSignature.chainValue lay := by
  obtain ⟨leftPart, hleftEval, hleftCounter, hleftValues⟩ :=
    left.signature_part_of_digest leftDigest lay
  obtain ⟨rightPart, hrightEval, hrightCounter, hrightValues⟩ :=
    right.signature_part_of_digest rightDigest lay
  have hpart : leftPart = rightPart := by
    rw [signLayer_eq_of_position_eq secretKey leftIndex rightIndex lay htree hleaf] at hleftEval
    exact Option.some.inj (hleftEval.symm.trans hrightEval)
  subst rightPart
  exact ⟨hleftCounter.trans hrightCounter.symm, hleftValues.trans hrightValues.symm⟩

end SphincsSecurity.Concrete
