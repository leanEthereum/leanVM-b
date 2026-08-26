import SphincsSecurity.Proof.LazyRevealProbe
import SphincsSecurity.Proof.SecretProbeTerminal

/-!
# Opaque one-time chain values

The lazy one-time simulation gives a separate opaque cell to every chain start and every structural
oracle answer. An ordinary chain query probes the value at its starting digit. A leaf query probes
chain zero's endpoint, which is the only endpoint needed by the fresh-opening extraction; a backward
opening always starts strictly before the endpoint and is therefore caught by a chain query.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

inductive Coordinate where
  | chainStart (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (chainIdx : ChainIndex)
  | position (position : Position)
deriving DecidableEq

structure Probe where
  coordinate : Coordinate
  candidate : Digest
deriving DecidableEq

noncomputable def Probe.target (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : Probe) : Digest :=
  match probe.coordinate with
  | .chainStart lay tree leafIdx chainIdx => otsSecret lay tree leafIdx chainIdx
  | .position position => honestValue f parameter otsSecret ftsSecret position

def Probe.Hits (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : Probe) : Prop :=
  probe.candidate = probe.target f parameter otsSecret ftsSecret

noncomputable def toProbe (probe : OtsValueProbe) : Probe :=
  if hzero : probe.digit.val = 0 then
    ⟨.chainStart probe.lay probe.tree probe.leafIdx probe.chainIdx, probe.candidate⟩
  else
    let step : ChainStep := ⟨probe.digit.val - 1, by
      have := probe.digit.isLt
      simp only [chainLength, winternitzBits] at this ⊢
      omega⟩
    ⟨.position (.chain probe.lay probe.tree probe.leafIdx probe.chainIdx step),
      probe.candidate⟩

@[simp] theorem toProbe_candidate (probe : OtsValueProbe) :
    (toProbe probe).candidate = probe.candidate := by
  unfold toProbe
  split <;> rfl

theorem toProbe_target
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (probe : OtsValueProbe) :
    (toProbe probe).target f parameter otsSecret ftsSecret =
      probe.target f parameter otsSecret := by
  unfold toProbe
  split_ifs with hzero
  · simp only [Probe.target]
    exact (probe.target_zero hzero).symm
  · simp only [Probe.target]
    let step : ChainStep := ⟨probe.digit.val - 1, by
      have := probe.digit.isLt
      simp only [chainLength, winternitzBits] at this ⊢
      omega⟩
    have hdigit : probe.digit.val = step.val + 1 := by
      simp only [step]
      omega
    exact (probe.target_succ hdigit).symm

theorem toProbe_hits
    {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest} {probe : OtsValueProbe}
    (hhit : probe.Hits f parameter otsSecret) :
    (toProbe probe).Hits f parameter otsSecret ftsSecret := by
  rw [Probe.Hits, toProbe_target]
  simpa only [toProbe_candidate, OtsValueProbe.Hits] using hhit

def Probe.MatchesInput (parameter : PublicParameter) (probe : Probe)
    (input : HashInput) : Prop :=
  match probe.coordinate with
  | .chainStart lay tree leafIdx chainIdx =>
      ∃ step : ChainStep, step.val = 0 ∧
        input = tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step)
          (digestBytes probe.candidate)
  | .position (.chain lay tree leafIdx chainIdx step) =>
      if _hnext : step.val + 1 < chainLength - 1 then
        ∃ nextStep : ChainStep, nextStep.val = step.val + 1 ∧
          input = tweakableHashInput parameter
            (.chain lay tree leafIdx chainIdx nextStep) (digestBytes probe.candidate)
      else
        chainIdx.val = 0 ∧ ∃ payload : HashInput,
          input = tweakableHashInput parameter (.leaf lay tree leafIdx) payload ∧
            slotDigest 0 input = probe.candidate
  | .position _ => False

noncomputable def Probe.outputCoordinate (probe : Probe) : Coordinate :=
  match probe.coordinate with
  | .chainStart lay tree leafIdx chainIdx =>
      .position (.chain lay tree leafIdx chainIdx
        ⟨0, by norm_num [chainLength, winternitzBits]⟩)
  | .position (.chain lay tree leafIdx chainIdx step) =>
      if hnext : step.val + 1 < chainLength - 1 then
        .position (.chain lay tree leafIdx chainIdx ⟨step.val + 1, hnext⟩)
      else
        .position (.leaf lay tree leafIdx)
  | .position position => .position position

theorem Probe.target_ftsSecret_irrel_of_matchesInput
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (left right : Index → FtsTree → FtsLeaf → Digest)
    (probe : Probe) (input : HashInput) (hmatch : probe.MatchesInput parameter input) :
    probe.target f parameter otsSecret left =
      probe.target f parameter otsSecret right := by
  cases probe with
  | mk coordinate candidate =>
      cases coordinate with
      | chainStart => rfl
      | position position =>
          cases position <;> simp only [Probe.MatchesInput] at hmatch
          case chain => rfl

theorem toProbe_matchesInput
    (parameter : PublicParameter) (probe : OtsValueProbe) (input : HashInput)
    (hmatch : probe.MatchesInput parameter input) :
    (toProbe probe).MatchesInput parameter input := by
  rcases hmatch with hchain | hleaf
  · obtain ⟨step, hdigit, hinput⟩ := hchain
    by_cases hzero : probe.digit.val = 0
    · have hto : toProbe probe =
          ⟨.chainStart probe.lay probe.tree probe.leafIdx probe.chainIdx,
            probe.candidate⟩ := by
        unfold toProbe
        rw [dif_pos hzero]
      rw [hto]
      simp only [Probe.MatchesInput]
      exact ⟨step, hdigit.symm.trans hzero, hinput⟩
    ·
      let previous : ChainStep := ⟨probe.digit.val - 1, by
        have := probe.digit.isLt
        simp only [chainLength, winternitzBits] at this ⊢
        omega⟩
      have hto : toProbe probe =
          ⟨.position (.chain probe.lay probe.tree probe.leafIdx probe.chainIdx previous),
            probe.candidate⟩ := by
        unfold toProbe
        rw [dif_neg hzero]
      have hnext : previous.val + 1 < chainLength - 1 := by
        simp only [previous]
        have := step.isLt
        omega
      rw [hto]
      simp only [Probe.MatchesInput]
      rw [dif_pos hnext]
      exact ⟨step, by simp only [previous]; omega, hinput⟩
  · obtain ⟨hdigit, hchain, payload, hinput, hslot⟩ := hleaf
    have hnonzero : probe.digit.val ≠ 0 := by
      simp only [chainLength, winternitzBits] at hdigit
      omega
    let previous : ChainStep := ⟨probe.digit.val - 1, by
      have := probe.digit.isLt
      simp only [chainLength, winternitzBits] at this ⊢
      omega⟩
    have hto : toProbe probe =
        ⟨.position (.chain probe.lay probe.tree probe.leafIdx probe.chainIdx previous),
          probe.candidate⟩ := by
      unfold toProbe
      rw [dif_neg hnonzero]
    have hlast : ¬previous.val + 1 < chainLength - 1 := by
      simp only [previous]
      omega
    rw [hto]
    simp only [Probe.MatchesInput]
    rw [dif_neg hlast]
    exact ⟨hchain, payload, hinput, hslot⟩

theorem FreshLayerOpening.exists_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hfresh : FreshLayerOpening f cache secretKey signingLog) :
    ∃ (probe : Probe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret (fun _ _ _ => 0) ∧
        probe.MatchesInput secretKey.parameter input ∧ cache input ≠ none := by
  obtain ⟨valueProbe, input, hhit, hunsigned, hmatch, hcached⟩ :=
    hfresh.exists_hit_probe_cached
  exact ⟨toProbe valueProbe, input, toProbe_hits hhit,
    toProbe_matchesInput secretKey.parameter valueProbe input hmatch, hcached⟩

theorem BackwardChainOpening.exists_matching_probe
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hbackward : BackwardChainOpening f cache secretKey signingLog) :
    ∃ (probe : Probe) (input : HashInput),
      probe.Hits f secretKey.parameter secretKey.otsSecret (fun _ _ _ => 0) ∧
        probe.MatchesInput secretKey.parameter input ∧ cache input ≠ none := by
  obtain ⟨valueProbe, signedDigit, input, hhit, hlt, hmatch, hcached⟩ :=
    hbackward.exists_hit_probe_cached
  exact ⟨toProbe valueProbe, input, toProbe_hits hhit,
    toProbe_matchesInput secretKey.parameter valueProbe input hmatch, hcached⟩

theorem cleanFreshEvent_exists_matching_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hevent : cleanFreshEvent parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : Probe) (input : HashInput),
      result.2.cache.AgreesWithFn f ∧
        probe.Hits f parameter otsSecret ftsSecret ∧
        probe.MatchesInput parameter input ∧ result.2.cache input ≠ none := by
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hfresh⟩ := hevent.2
  obtain ⟨probe, input, hhit, hmatch, hcached⟩ :=
    SphincsSecurity.Concrete.OtsProbeSimulation.FreshLayerOpening.exists_matching_probe hfresh
  refine ⟨f, probe, input, hf, ?_, hmatch, hcached⟩
  rw [Probe.Hits] at hhit ⊢
  rw [← probe.target_ftsSecret_irrel_of_matchesInput f parameter otsSecret
    (fun _ _ _ => 0) ftsSecret input hmatch]
  exact hhit

theorem cleanBackwardEvent_exists_matching_probe
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {result : (Digest × Forgery × Bool) × ViewedFullTraceState}
    (hevent : cleanBackwardEvent parameter otsSecret ftsSecret result) :
    ∃ (f : QueryImpl HashSpec Id) (probe : Probe) (input : HashInput),
      result.2.cache.AgreesWithFn f ∧
        probe.Hits f parameter otsSecret ftsSecret ∧
        probe.MatchesInput parameter input ∧ result.2.cache input ≠ none := by
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hbackward⟩ := hevent.2
  obtain ⟨probe, input, hhit, hmatch, hcached⟩ :=
    SphincsSecurity.Concrete.OtsProbeSimulation.BackwardChainOpening.exists_matching_probe
      hbackward
  refine ⟨f, probe, input, hf, ?_, hmatch, hcached⟩
  rw [Probe.Hits] at hhit ⊢
  rw [← probe.target_ftsSecret_irrel_of_matchesInput f parameter otsSecret
    (fun _ _ _ => 0) ftsSecret input hmatch]
  exact hhit

theorem chainProbeInput_eq_iff (parameter : PublicParameter)
    (leftLay rightLay : Layer) (leftTree rightTree : TreeIndex)
    (leftLeaf rightLeaf : LeafIndex) (leftChain rightChain : ChainIndex)
    (leftStep rightStep : ChainStep) (leftCandidate rightCandidate : Digest) :
    tweakableHashInput parameter
        (.chain leftLay leftTree leftLeaf leftChain leftStep) (digestBytes leftCandidate) =
      tweakableHashInput parameter
        (.chain rightLay rightTree rightLeaf rightChain rightStep) (digestBytes rightCandidate) ↔
      leftLay = rightLay ∧ leftTree = rightTree ∧ leftLeaf = rightLeaf ∧
        leftChain = rightChain ∧ leftStep = rightStep ∧ leftCandidate = rightCandidate := by
  constructor
  · intro heq
    have hparts := tweakableHashInput_injective parameter (by trivial) (by trivial) heq
    simp only [HashDomain.chain.injEq] at hparts
    exact ⟨hparts.1.1, hparts.1.2.1, hparts.1.2.2.1, hparts.1.2.2.2.1,
      hparts.1.2.2.2.2, digestBytes_injective hparts.2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem chainProbeInput_ne_leafInput (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) (candidate : Digest)
    (leafLay : Layer) (leafTree : TreeIndex) (leaf : LeafIndex) (payload : HashInput) :
    tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step)
        (digestBytes candidate) ≠
      tweakableHashInput parameter (.leaf leafLay leafTree leaf) payload := by
  intro heq
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).1
  simp at hdomain

theorem leafInput_domain_eq (parameter : PublicParameter)
    (leftLay rightLay : Layer) (leftTree rightTree : TreeIndex)
    (leftLeaf rightLeaf : LeafIndex) (leftPayload rightPayload : HashInput)
    (heq : tweakableHashInput parameter (.leaf leftLay leftTree leftLeaf) leftPayload =
      tweakableHashInput parameter (.leaf rightLay rightTree rightLeaf) rightPayload) :
    leftLay = rightLay ∧ leftTree = rightTree ∧ leftLeaf = rightLeaf := by
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).1
  simpa only [HashDomain.leaf.injEq] using hdomain

theorem Probe.matchesInput_unique (parameter : PublicParameter) (input : HashInput)
    {left right : Probe} (hleft : left.MatchesInput parameter input)
    (hright : right.MatchesInput parameter input) : left = right := by
  rcases left with ⟨leftCoordinate, leftCandidate⟩
  rcases right with ⟨rightCoordinate, rightCandidate⟩
  cases leftCoordinate with
  | chainStart leftLay leftTree leftLeaf leftChain =>
      obtain ⟨leftStep, hleftZero, hleftInput⟩ := hleft
      cases rightCoordinate with
      | chainStart rightLay rightTree rightLeaf rightChain =>
          obtain ⟨rightStep, hrightZero, hrightInput⟩ := hright
          have hparts := (chainProbeInput_eq_iff parameter leftLay rightLay leftTree rightTree
            leftLeaf rightLeaf leftChain rightChain leftStep rightStep leftCandidate
            rightCandidate).1 (hleftInput.symm.trans hrightInput)
          rcases hparts with ⟨rfl, rfl, rfl, rfl, hstep, rfl⟩
          rfl
      | position rightPosition =>
          cases rightPosition with
          | chain rightLay rightTree rightLeaf rightChain rightStep =>
              simp only [Probe.MatchesInput] at hright
              by_cases hrightNext : rightStep.val + 1 < chainLength - 1
              · rw [dif_pos hrightNext] at hright
                obtain ⟨nextStep, hnext, hrightInput⟩ := hright
                have hparts := (chainProbeInput_eq_iff parameter leftLay rightLay leftTree
                  rightTree leftLeaf rightLeaf leftChain rightChain leftStep nextStep
                  leftCandidate rightCandidate).1 (hleftInput.symm.trans hrightInput)
                rcases hparts with ⟨hlay, htree, hleaf, hchain, hstep, hcandidate⟩
                have hstepVal := congrArg Fin.val hstep
                omega
              · rw [dif_neg hrightNext] at hright
                obtain ⟨hchain, payload, hrightInput, hslot⟩ := hright
                exact (chainProbeInput_ne_leafInput parameter leftLay leftTree leftLeaf leftChain
                  leftStep leftCandidate rightLay rightTree rightLeaf payload
                  (hleftInput.symm.trans hrightInput)).elim
          | leaf | node | ftsLeaf | ftsNode | ftsRoots => simp [Probe.MatchesInput] at hright
  | position leftPosition =>
      cases leftPosition with
      | chain leftLay leftTree leftLeaf leftChain leftStep =>
          simp only [Probe.MatchesInput] at hleft
          cases rightCoordinate with
          | chainStart rightLay rightTree rightLeaf rightChain =>
              obtain ⟨rightStartStep, hrightZero, hrightInput⟩ := hright
              by_cases hleftNext : leftStep.val + 1 < chainLength - 1
              · rw [dif_pos hleftNext] at hleft
                obtain ⟨leftNextStep, hnext, hleftInput⟩ := hleft
                have hparts := (chainProbeInput_eq_iff parameter leftLay rightLay leftTree
                  rightTree leftLeaf rightLeaf leftChain rightChain leftNextStep rightStartStep
                  leftCandidate rightCandidate).1 (hleftInput.symm.trans hrightInput)
                rcases hparts with ⟨hlay, htree, hleaf, hchain, hstep, hcandidate⟩
                have hstepVal := congrArg Fin.val hstep
                omega
              · rw [dif_neg hleftNext] at hleft
                obtain ⟨hchain, payload, hleftInput, hslot⟩ := hleft
                exact (chainProbeInput_ne_leafInput parameter rightLay rightTree rightLeaf
                  rightChain rightStartStep rightCandidate leftLay leftTree leftLeaf payload
                  (hrightInput.symm.trans hleftInput)).elim
          | position rightPosition =>
              cases rightPosition with
              | chain rightLay rightTree rightLeaf rightChain rightStep =>
                  simp only [Probe.MatchesInput] at hright
                  by_cases hleftNext : leftStep.val + 1 < chainLength - 1
                  · by_cases hrightNext : rightStep.val + 1 < chainLength - 1
                    · rw [dif_pos hleftNext] at hleft
                      rw [dif_pos hrightNext] at hright
                      obtain ⟨leftNext, hleftNextValue, hleftInput⟩ := hleft
                      obtain ⟨rightNext, hrightNextValue, hrightInput⟩ := hright
                      have hparts := (chainProbeInput_eq_iff parameter leftLay rightLay leftTree
                        rightTree leftLeaf rightLeaf leftChain rightChain leftNext rightNext
                        leftCandidate rightCandidate).1 (hleftInput.symm.trans hrightInput)
                      rcases hparts with ⟨hlay, htree, hleaf, hchain, hnextStep, hcandidate⟩
                      have hnextValue := congrArg Fin.val hnextStep
                      have hstep : leftStep = rightStep := Fin.ext (by omega)
                      cases hlay
                      cases htree
                      cases hleaf
                      cases hchain
                      cases hstep
                      cases hcandidate
                      rfl
                    · rw [dif_pos hleftNext] at hleft
                      rw [dif_neg hrightNext] at hright
                      obtain ⟨leftNext, hleftNextValue, hleftInput⟩ := hleft
                      obtain ⟨hchain, payload, hrightInput, hslot⟩ := hright
                      exact (chainProbeInput_ne_leafInput parameter leftLay leftTree leftLeaf
                        leftChain leftNext leftCandidate rightLay rightTree rightLeaf payload
                        (hleftInput.symm.trans hrightInput)).elim
                  · by_cases hrightNext : rightStep.val + 1 < chainLength - 1
                    · rw [dif_neg hleftNext] at hleft
                      rw [dif_pos hrightNext] at hright
                      obtain ⟨hchain, payload, hleftInput, hslot⟩ := hleft
                      obtain ⟨rightNext, hrightNextValue, hrightInput⟩ := hright
                      exact (chainProbeInput_ne_leafInput parameter rightLay rightTree rightLeaf
                        rightChain rightNext rightCandidate leftLay leftTree leftLeaf payload
                        (hrightInput.symm.trans hleftInput)).elim
                    · rw [dif_neg hleftNext] at hleft
                      rw [dif_neg hrightNext] at hright
                      obtain ⟨hleftChain, leftPayload, hleftInput, hleftSlot⟩ := hleft
                      obtain ⟨hrightChain, rightPayload, hrightInput, hrightSlot⟩ := hright
                      have hparts := leafInput_domain_eq parameter leftLay rightLay leftTree
                        rightTree leftLeaf rightLeaf leftPayload rightPayload
                        (hleftInput.symm.trans hrightInput)
                      rcases hparts with ⟨hlay, htree, hleaf⟩
                      have hchain : leftChain = rightChain :=
                        Fin.ext (hleftChain.trans hrightChain.symm)
                      have hstep : leftStep = rightStep := by
                        apply Fin.ext
                        have hleftLt := leftStep.isLt
                        have hrightLt := rightStep.isLt
                        omega
                      have hcandidate : leftCandidate = rightCandidate :=
                        hleftSlot.symm.trans hrightSlot
                      cases hlay
                      cases htree
                      cases hleaf
                      cases hchain
                      cases hstep
                      cases hcandidate
                      rfl
              | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
                  simp [Probe.MatchesInput] at hright
      | leaf | node | ftsLeaf | ftsNode | ftsRoots => simp [Probe.MatchesInput] at hleft

noncomputable def decodeProbe? (parameter : PublicParameter) (input : HashInput) :
    Option Probe := by
  classical
  exact if hexists : ∃ probe : Probe, probe.MatchesInput parameter input then
    some hexists.choose
  else none

theorem decodeProbe?_eq_none_iff (parameter : PublicParameter) (input : HashInput) :
    decodeProbe? parameter input = none ↔
      ∀ probe : Probe, ¬probe.MatchesInput parameter input := by
  classical
  constructor
  · intro hdecode probe hmatch
    have hexists : ∃ candidate : Probe, candidate.MatchesInput parameter input :=
      ⟨probe, hmatch⟩
    unfold decodeProbe? at hdecode
    rw [dif_pos hexists] at hdecode
    simp at hdecode
  · intro hnone
    unfold decodeProbe?
    rw [dif_neg]
    rintro ⟨probe, hmatch⟩
    exact hnone probe hmatch

theorem decodeProbe?_eq_some_iff (parameter : PublicParameter) (input : HashInput)
    (probe : Probe) :
    decodeProbe? parameter input = some probe ↔ probe.MatchesInput parameter input := by
  classical
  unfold decodeProbe?
  split_ifs with hexists
  · constructor
    · intro heq
      have hchosen : hexists.choose = probe := by simpa using heq
      simpa [← hchosen] using hexists.choose_spec
    · intro hmatch
      have hchosen : hexists.choose = probe :=
        Probe.matchesInput_unique parameter input hexists.choose_spec hmatch
      simp [hchosen]
  · constructor
    · simp
    · intro hmatch
      exact (hexists ⟨probe, hmatch⟩).elim

inductive SplitHashKey where
  | ordinary (input : HashInput)
  | hidden (coordinate : Coordinate)
deriving DecidableEq

abbrev SplitHashCache := SplitHashKey → Option HashOutput

def emptySplitHashCache : SplitHashCache := fun _ => none

noncomputable def completedSplitHashCache (table : Coordinate → HashOutput)
    (cache : SplitHashCache) : SplitHashCache
  | .ordinary input => cache (.ordinary input)
  | .hidden coordinate =>
      match cache (.hidden coordinate) with
      | some output => some output
      | none => some (table coordinate)

noncomputable def mergedCache (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (cache : SplitHashCache) : QueryCache HashSpec :=
  fun input =>
    match decodeProbe? parameter input with
    | some candidate =>
        if candidate.candidate = truncateHash (table candidate.coordinate) then
          completedSplitHashCache table cache (.hidden candidate.outputCoordinate)
        else
          cache (.ordinary input)
    | none => cache (.ordinary input)

@[simp] theorem mergedCache_empty_ordinary (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (input : HashInput)
    (hdecode : decodeProbe? parameter input = none) :
    mergedCache parameter table emptySplitHashCache input = none := by
  simp [mergedCache, hdecode, emptySplitHashCache]

theorem mergedCache_matching_probe (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (cache : SplitHashCache)
    (candidate : Probe) (input : HashInput)
    (hmatch : candidate.MatchesInput parameter input)
    (hhit : candidate.candidate = truncateHash (table candidate.coordinate)) :
    mergedCache parameter table cache input =
      completedSplitHashCache table cache (.hidden candidate.outputCoordinate) := by
  simp [mergedCache, (decodeProbe?_eq_some_iff parameter input candidate).2 hmatch, hhit]

theorem mergedCache_nonmatching_probe (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (cache : SplitHashCache)
    (candidate : Probe) (input : HashInput)
    (hmatch : candidate.MatchesInput parameter input)
    (hmiss : candidate.candidate ≠ truncateHash (table candidate.coordinate)) :
    mergedCache parameter table cache input = cache (.ordinary input) := by
  simp [mergedCache, (decodeProbe?_eq_some_iff parameter input candidate).2 hmatch, hmiss]

noncomputable def splitHashQuery (key : SplitHashKey) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  let cache ← get
  match cache key with
  | some output => pure output
  | none =>
      let output ← liftM (LazyRevealProbe.hashOutputQuery (Coordinate := Coordinate))
      set (Function.update cache key (some output))
      pure output

noncomputable def probe (candidate : Probe) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit :=
  liftM (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate)

noncomputable def probingHashQuery (parameter : PublicParameter) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  match decodeProbe? parameter input with
  | some candidate => probe candidate
  | none => pure ()
  splitHashQuery (.ordinary input)

noncomputable def probingHashImpl (parameter : PublicParameter) :
    QueryImpl HashSpec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  fun input => probingHashQuery parameter input

noncomputable def ordinaryHashImpl :
    QueryImpl HashSpec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  fun input => splitHashQuery (.ordinary input)

noncomputable def splitUniformImpl :
    QueryImpl unifSpec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  fun n => liftM (LazyRevealProbe.uniformQuery (Coordinate := Coordinate) n)

noncomputable def probingRomImpl (parameter : PublicParameter) :
    QueryImpl OracleWorld
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  splitUniformImpl + probingHashImpl parameter

noncomputable def ordinaryRomImpl :
    QueryImpl OracleWorld
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  splitUniformImpl + ordinaryHashImpl

end SphincsSecurity.Concrete.OtsProbeSimulation
