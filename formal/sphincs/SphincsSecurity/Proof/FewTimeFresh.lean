import SphincsSecurity.Proof.FewTimePadding

/-!
# Fresh signer views

During a digest retry loop, every message input added after the loop's reference cache contains an
inadmissible answer. Thus a successful input absent from the reference cache is answered freshly,
and its retained few-time view has the uniform distribution even after all failed retries.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev HashOutputRest :=
  FtsLeaf × BitVec (hashOutputBits - messageDigestBits)

def reorderHashOutputCoordinates :
    (HashOutputRest × FewTimeView) ≃ HashOutputCoordinates where
  toFun value := ((value.2, value.1.1), value.1.2)
  invFun value := ((value.1.2, value.2), value.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxRecDepth 100000 in
theorem evalDist_uniformHashOutputCoordinates_bind_reordered {Result : Type}
    (continuation : HashOutputCoordinates → ProbComp Result) :
    𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>= continuation] =
      𝒟[($ᵗ HashOutputRest : ProbComp HashOutputRest) >>= fun rest =>
        ($ᵗ FewTimeView : ProbComp FewTimeView) >>= fun view =>
          continuation ((view, rest.1), rest.2)] := by
  let paired : ProbComp (HashOutputRest × FewTimeView) := do
    let rest ← $ᵗ HashOutputRest
    let view ← $ᵗ FewTimeView
    pure (rest, view)
  have hpaired :
      𝒟[paired] = 𝒟[($ᵗ (HashOutputRest × FewTimeView) :
        ProbComp (HashOutputRest × FewTimeView))] := by
    exact evalDist_independent_uniform_pair
  have hreordered :
      𝒟[reorderHashOutputCoordinates <$> paired] =
        𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
    calc
      𝒟[reorderHashOutputCoordinates <$> paired] =
          reorderHashOutputCoordinates <$> 𝒟[paired] := by rw [evalDist_map]
      _ = reorderHashOutputCoordinates <$>
          𝒟[($ᵗ (HashOutputRest × FewTimeView) :
            ProbComp (HashOutputRest × FewTimeView))] := by rw [hpaired]
      _ = 𝒟[reorderHashOutputCoordinates <$>
          ($ᵗ (HashOutputRest × FewTimeView) :
            ProbComp (HashOutputRest × FewTimeView))] := by rw [evalDist_map]
      _ = 𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] :=
        evalDist_map_bijective_uniform_cross
          (α := HashOutputRest × FewTimeView) (β := HashOutputCoordinates)
          (reorderHashOutputCoordinates : HashOutputRest × FewTimeView →
            HashOutputCoordinates)
          reorderHashOutputCoordinates.bijective
  calc
    𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>= continuation] =
        𝒟[(reorderHashOutputCoordinates <$> paired) >>= continuation] := by
      rw [evalDist_bind, ← hreordered, ← evalDist_bind]
    _ = _ := by
      simp only [paired, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        reorderHashOutputCoordinates, Function.comp_apply]
      rfl

theorem probEvent_uniformDigestCoordinates_admissible_view
    (P : FewTimeView → Prop) :
    Pr[fun coordinates : FewTimeView × FtsLeaf => coordinates.2 = 0 ∧ P coordinates.1 |
      ($ᵗ (FewTimeView × FtsLeaf) : ProbComp (FewTimeView × FtsLeaf))] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  change Pr[fun coordinates : FewTimeView × FtsLeaf =>
      coordinates.2 = 0 ∧ P coordinates.1 |
    Prod.mk <$> ($ᵗ FewTimeView : ProbComp FewTimeView) <*>
      ($ᵗ FtsLeaf : ProbComp FtsLeaf)] = _
  calc
    _ = Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          Pr[fun leaf : FtsLeaf => leaf = 0 |
            ($ᵗ FtsLeaf : ProbComp FtsLeaf)] := by
      apply probEvent_seq_map_eq_mul
      intro view _hview leaf _hleaf
      simp [and_comm]
    _ = Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ := by
      rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, Fintype.card_fin]
    _ = _ := by rw [mul_comm]

set_option maxRecDepth 100000 in
theorem probEvent_uniformHashOutput_admissible_view
    (P : FewTimeView → Prop) :
    Pr[fun output : HashOutput =>
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  let coordinates : HashOutput → FewTimeView × FtsLeaf := fun output =>
    digestCoordinates (truncateMessageDigest output)
  let event : FewTimeView × FtsLeaf → Prop := fun value => value.2 = 0 ∧ P value.1
  calc
    Pr[fun output : HashOutput =>
        signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output) |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        Pr[event | coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [probEvent_map]
      congr 1
      funext output
      rw [signAttemptResultOfOutput_ne_none_iff]
      rfl
    _ = Pr[event |
        ($ᵗ (FewTimeView × FtsLeaf) : ProbComp (FewTimeView × FtsLeaf))] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (by
        simpa only [coordinates] using evalDist_hashOutput_digestCoordinates_uniform)
    _ = _ := probEvent_uniformDigestCoordinates_admissible_view P

theorem probEvent_randomOracle_fresh_admissible_view
    (input : HashInput) (cache : QueryCache HashSpec) (hcache : cache input = none)
    (P : FewTimeView → Prop) :
    Pr[fun result : HashOutput × QueryCache HashSpec =>
      signAttemptResultOfOutput result.1 ≠ none ∧
        P (hashOutputFewTimeView result.1) |
      (randomOracle input).run cache] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hcache]
  change Pr[fun result : HashOutput × QueryCache HashSpec =>
      signAttemptResultOfOutput result.1 ≠ none ∧
        P (hashOutputFewTimeView result.1) |
    (fun output : HashOutput => (output, cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  rw [probEvent_map]
  exact probEvent_uniformHashOutput_admissible_view P

def OnlyRejectedNewMessageEntries (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) : Prop :=
  ∀ randomness output,
    referenceCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none →
    workingCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output →
    signAttemptResultOfOutput output = none

theorem onlyRejectedNewMessageEntries_self (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) :
    OnlyRejectedNewMessageEntries cache cache secretKey message := by
  intro randomness output hmiss hhit
  rw [hmiss] at hhit
  simp at hhit

theorem onlyRejectedNewMessageEntries_cacheRejected
    (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (sampled : Randomness)
    (output : HashOutput)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache secretKey message)
    (hrejected : signAttemptResultOfOutput output = none) :
    OnlyRejectedNewMessageEntries referenceCache
      (workingCache.cacheQuery
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message sampled)) output)
      secretKey message := by
  intro randomness found hreferenceFound hfound
  let foundInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : foundInput = sampledInput
  · have hfound' : some output = some found := by
      calc
        some output =
            (workingCache.cacheQuery sampledInput output) sampledInput := by
              rw [QueryCache.cacheQuery_self]
        _ = (workingCache.cacheQuery sampledInput output) foundInput := by rw [hsame]
        _ = some found := by simpa only [foundInput, sampledInput] using hfound
    rw [← Option.some.inj hfound']
    exact hrejected
  · have hworking : workingCache foundInput = some found := by
      rw [QueryCache.cacheQuery_of_ne workingCache output hsame] at hfound
      simpa only [foundInput, sampledInput] using hfound
    exact hinvariant randomness found hreferenceFound hworking

set_option maxRecDepth 100000 in
theorem onlyRejectedNewMessageEntries_of_failed_attempt
    (referenceCache beforeCache afterCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (sampled : Randomness)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache beforeCache secretKey message)
    (hmem : (none, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message sampled)).run beforeCache)) :
    OnlyRejectedNewMessageEntries referenceCache afterCache secretKey message := by
  intro randomness output hreference hafter
  let target := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : target = sampledInput
  · apply Eq.symm
    have hafterSampled : afterCache sampledInput = some output := by
      change afterCache target = some output at hafter
      rw [← hsame]
      exact hafter
    change afterCache
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message sampled)) = some output at hafterSampled
    exact signAttempt_result_of_cached secretKey message sampled beforeCache afterCache
      none output hafterSampled hmem
  · by_cases hbefore : beforeCache target = none
    · change beforeCache
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = none at hbefore
      change (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) ≠
        tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message sampled) at hsame
      have hnone := signAttempt_cache_other_none secretKey message sampled beforeCache afterCache
        none hmem _ hbefore hsame
      rw [hnone] at hafter
      simp at hafter
    · obtain ⟨prior, hprior⟩ := Option.ne_none_iff_exists'.mp hbefore
      have hmemWorld : (none, afterCache) ∈ support
          ((simulateQ romImpl
            (liftM (signAttempt secretKey message sampled :
              OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
                OracleComp OracleWorld (Option (Index × (DigestTree → FtsLeaf))))).run
              beforeCache) := by
        rw [simulateQ_romImpl_liftM]
        exact hmem
      have hle : beforeCache ≤ afterCache :=
        simulateQ_romImpl_cache_le
          (liftM (signAttempt secretKey message sampled :
            OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
              OracleComp OracleWorld (Option (Index × (DigestTree → FtsLeaf))))
          beforeCache (none, afterCache) hmemWorld
      have heq : prior = output := Option.some.inj ((hle hprior).symm.trans hafter)
      rw [← heq]
      exact hinvariant randomness prior hreference hprior

def FreshSelectedView (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)) ×
      QueryCache HashSpec) : Prop :=
  ∃ randomness index leaves,
    result.1 = some (randomness, index, leaves)
      ∧ referenceCache (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)) = none
      ∧ P (selectedFewTimeView index leaves)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_signDigestLoop_freshSelectedView_le_uniform
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache secretKey message) :
    Pr[FreshSelectedView referenceCache secretKey message P |
      (simulateQ romImpl (signDigestLoop attempts secretKey message)).run workingCache] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  induction attempts generalizing workingCache with
  | zero =>
      refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
      intro result hresult hevent
      have hresultEq : result = (none, workingCache) := by
        simpa only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hresult
      obtain ⟨randomness, index, leaves, hselected, _⟩ := hevent
      rw [hresultEq] at hselected
      simp at hselected
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq]
      refine probEvent_bind_le_of_forall_le fun randomness _hrandomness => ?_
      let input := tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)
      by_cases hreference : referenceCache input = none
      · by_cases hworking : workingCache input = none
        · let continuation := signDigestLoopContinuation attempts secretKey message randomness
          have hcoordinates := evalDist_signAttempt_fresh_bind_coordinates
            secretKey message randomness workingCache (by simpa only [input] using hworking)
            continuation
          change Pr[FreshSelectedView referenceCache secretKey message P |
              (simulateQ randomOracle
                (signAttempt secretKey message randomness :
                  OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))).run
                workingCache >>= continuation] ≤ _
          have hprobCoordinates := probEvent_congr'
            (p := FreshSelectedView referenceCache secretKey message P)
            (q := FreshSelectedView referenceCache secretKey message P)
            (fun _ _ => Iff.rfl) hcoordinates
          rw [hprobCoordinates]
          have hreorder := evalDist_uniformHashOutputCoordinates_bind_reordered
            (fun coordinates =>
              let output := hashOutputCoordinatesEquiv.symm coordinates
              continuation (signAttemptResultOfOutput output,
                workingCache.cacheQuery input output))
          rw [probEvent_congr' (fun _ _ => Iff.rfl) hreorder]
          refine probEvent_bind_le_of_forall_le fun rest _hrest => ?_
          by_cases hadmissible : rest.1 = 0
          · refine (probEvent_bind_le_probEvent
              (p := P) (q := FreshSelectedView referenceCache secretKey message P) ?_).trans le_rfl
            intro view _hview hP
            refine probEvent_eq_zero ?_
            intro result hresult hevent
            let coordinates : HashOutputCoordinates := ((view, rest.1), rest.2)
            let output := hashOutputCoordinatesEquiv.symm coordinates
            have hsuccessful : signAttemptResultOfOutput output ≠ none := by
              rw [signAttemptResultOfOutput_coordinates_ne_none_iff]
              exact hadmissible
            obtain ⟨indexLeaves, hindexLeaves⟩ := Option.ne_none_iff_exists'.mp hsuccessful
            rcases indexLeaves with ⟨index, leaves⟩
            have hviewEq : selectedFewTimeView index leaves = view := by
              exact signAttemptResultOfOutput_coordinates_view coordinates index leaves
                (by simpa only [output] using hindexLeaves)
            have hresultEq : result =
                (some (randomness, index, leaves),
                  workingCache.cacheQuery input output) := by
              simpa only [continuation, signDigestLoopContinuation, hindexLeaves,
                support_pure, Set.mem_singleton_iff, coordinates, output] using hresult
            obtain ⟨foundRandomness, foundIndex, foundLeaves, hselected, _, hpattern⟩ := hevent
            have hselected' :
                (foundRandomness, foundIndex, foundLeaves) =
                  (randomness, index, leaves) := by
              apply Option.some.inj
              exact hselected.symm.trans (congrArg Prod.fst hresultEq)
            obtain ⟨rfl, rfl, rfl⟩ := hselected'
            apply hP
            rw [hviewEq] at hpattern
            exact hpattern
          · refine probEvent_bind_le_of_forall_le fun view _hview => ?_
            let coordinates : HashOutputCoordinates := ((view, rest.1), rest.2)
            let output := hashOutputCoordinatesEquiv.symm coordinates
            have hrejected : signAttemptResultOfOutput output = none := by
              apply Option.eq_none_iff_forall_not_mem.mpr
              intro selected hselected
              have hne : signAttemptResultOfOutput output ≠ none := by
                rw [hselected]
                simp
              rw [signAttemptResultOfOutput_coordinates_ne_none_iff] at hne
              exact hadmissible hne
            have hinvariant' := onlyRejectedNewMessageEntries_cacheRejected
              referenceCache workingCache secretKey message randomness output hinvariant
              hrejected
            simpa only [coordinates, output, continuation, hrejected,
              signDigestLoopContinuation] using
              ih (workingCache.cacheQuery input output) hinvariant'
        · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hworking
          have hrejected := hinvariant randomness output
            (by simpa only [input] using hreference) (by simpa only [input] using houtput)
          refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
          have hle : workingCache ≤ attemptResult.2 :=
            simulateQ_romImpl_cache_le
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
                  OracleComp OracleWorld (Option (Index × (DigestTree → FtsLeaf))))
              workingCache attemptResult (by
                rw [simulateQ_romImpl_liftM]
                exact hattempt)
          have hattemptResult : attemptResult.1 = none :=
            (signAttempt_result_of_cached secretKey message randomness workingCache
              attemptResult.2 attemptResult.1 output
              (hle (by simpa only [input] using houtput)) hattempt).trans hrejected
          have hinvariant' := onlyRejectedNewMessageEntries_of_failed_attempt
            referenceCache workingCache attemptResult.2 secretKey message randomness
            hinvariant (by
              have heq : attemptResult = (none, attemptResult.2) :=
                Prod.ext hattemptResult rfl
              rw [← heq]
              exact hattempt)
          simpa only [hattemptResult, signDigestLoopContinuation] using
            ih attemptResult.2 hinvariant'
      · refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
        cases hattemptResult : attemptResult.1 with
        | none =>
            have hinvariant' := onlyRejectedNewMessageEntries_of_failed_attempt
              referenceCache workingCache attemptResult.2 secretKey message randomness
              hinvariant (by
                have heq : attemptResult = (none, attemptResult.2) :=
                  Prod.ext hattemptResult rfl
                rw [← heq]
                exact hattempt)
            simpa only [hattemptResult, signDigestLoopContinuation] using
              ih attemptResult.2 hinvariant'
        | some selected =>
            refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
            intro result hresult hevent
            rcases selected with ⟨index, leaves⟩
            have hresultEq : result =
                (some (randomness, index, leaves), attemptResult.2) := by
              simpa only [hattemptResult, signDigestLoopContinuation, support_pure,
                Set.mem_singleton_iff] using hresult
            obtain ⟨foundRandomness, foundIndex, foundLeaves, hselected, hmiss, _⟩ := hevent
            have hrandomness : foundRandomness = randomness := by
              have htuple : (foundRandomness, foundIndex, foundLeaves) =
                  (randomness, index, leaves) :=
                Option.some.inj (hselected.symm.trans (congrArg Prod.fst hresultEq))
              exact congrArg Prod.fst htuple
            rw [hrandomness] at hmiss
            exact hreference hmiss

def FreshSuccessfulSignerView (initialCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  ∃ signature view,
    result.1 = (some signature, some view)
      ∧ initialCache (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message signature.randomness)) = none
      ∧ P view

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_signWithView_freshSuccessful_le_uniform
    (secretKey : SecretKey) (message : Message) (initialCache : QueryCache HashSpec)
    (P : FewTimeView → Prop) :
    Pr[FreshSuccessfulSignerView initialCache secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  rw [signWithView, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent
    (p := FreshSelectedView initialCache secretKey message P) ?_).trans
    (probEvent_signDigestLoop_freshSelectedView_le_uniform digestAttemptLimit
      secretKey message initialCache initialCache P
      (onlyRejectedNewMessageEntries_self initialCache secretKey message))
  intro loopResult hloop hnotFresh
  cases hloopResult : loopResult.1 with
  | none =>
      refine probEvent_eq_zero ?_
      intro result hresult hevent
      have hresultEq : result = ((none, none), loopResult.2) := by
        simpa only [hloopResult, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hresult
      obtain ⟨signature, view, hsuccessful, _⟩ := hevent
      rw [hresultEq] at hsuccessful
      simp at hsuccessful
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      refine probEvent_eq_zero ?_
      intro result hresult hevent
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hresult
      have hpureEq : result =
          ((signatureResult, some (selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      obtain ⟨signature, view, hsuccessful, hmiss, hP⟩ := hevent
      have hpureFirst := congrArg Prod.fst hpureEq
      have hsignatureResult : signatureResult = some signature := by
        have := congrArg Prod.fst (hpureFirst.symm.trans hsuccessful)
        simpa using this
      have hview : view = selectedFewTimeView index leaves := by
        have := congrArg Prod.snd (hpureFirst.symm.trans hsuccessful)
        simpa using this.symm
      have hsignature' : (some signature, signatureCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAfterDigest secretKey randomness index leaves)).run loopResult.2) := by
        rw [hsignatureResult] at hsignature
        simpa only [simulateQ_romImpl_liftM] using hsignature
      have hrandomness := signAfterDigest_support_some_randomness secretKey randomness
        index leaves loopResult.2 signatureCache signature hsignature'
      apply hnotFresh
      refine ⟨randomness, index, leaves, hloopResult, ?_, ?_⟩
      · rw [← hrandomness]
        exact hmiss
      · rw [← hview]
        exact hP

end SphincsSecurity.Concrete
