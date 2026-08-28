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

def Probe.SourceSettled (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (probe : Probe) : Prop :=
  match probe.coordinate with
  | .chainStart _ _ _ _ => True
  | .position position =>
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position

theorem Probe.target_eq_of_sourceSettled
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {f g : QueryImpl HashSpec Id} {probe : Probe}
    (hf : cache.AgreesWithFn f) (hg : cache.AgreesWithFn g)
    (hsettled : probe.SourceSettled cache secretKey) :
    probe.target f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret =
      probe.target g secretKey.parameter secretKey.otsSecret secretKey.ftsSecret := by
  cases probe with
  | mk coordinate candidate =>
      cases coordinate with
      | chainStart => rfl
      | position position =>
          simp only [Probe.SourceSettled] at hsettled
          simp only [Probe.target]
          rw [honestValue_eq_of_settled hf hsettled,
            honestValue_eq_of_settled hg hsettled]

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

theorem toProbe_sourceSettled_of_layerRootSettled
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {probe : OtsValueProbe}
    (hleaf : probe.leafIdx.val < 2 ^ layerHeight probe.lay)
    (hroot : LayerRootSettled cache secretKey probe.lay probe.tree) :
    (toProbe probe).SourceSettled cache secretKey := by
  have hleaf := (settled_tree_path_of_settled_root probe.lay probe.tree probe.leafIdx
    hleaf hroot).1
  unfold toProbe
  split_ifs with hzero
  · trivial
  · simp only [Probe.SourceSettled]
    apply settled_chain_of_settled_leaf probe.lay probe.tree probe.leafIdx hleaf probe.chainIdx
      (probe.digit.val - 1)

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
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hfresh⟩ :=
    hevent.2.toViewed
  obtain ⟨probe, input, hhit, hmatch, hcached⟩ :=
    SphincsSecurity.Concrete.OtsProbeSimulation.FreshLayerOpening.exists_matching_probe
      hfresh.toForged.toFreshLayerOpening
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
  obtain ⟨f, digest, hf, hvalid, hnotContains, hdigest, hadmissible, hbackward⟩ :=
    hevent.2.toViewed
  obtain ⟨probe, input, hhit, hmatch, hcached⟩ :=
    SphincsSecurity.Concrete.OtsProbeSimulation.BackwardChainOpening.exists_matching_probe
      hbackward.toForged.toBackwardChainOpening
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

noncomputable def decodePosition? (parameter : PublicParameter) (input : HashInput) :
    Option Position := by
  classical
  exact if hexists : ∃ position : Position, AtPosition parameter input position then
    some hexists.choose
  else none

theorem decodePosition?_eq_some_iff (parameter : PublicParameter) (input : HashInput)
    (position : Position) :
    decodePosition? parameter input = some position ↔
      AtPosition parameter input position := by
  classical
  unfold decodePosition?
  split_ifs with hexists
  · constructor
    · intro heq
      have hchosen : hexists.choose = position := by simpa using heq
      simpa [← hchosen] using hexists.choose_spec
    · intro hposition
      have hchosen : hexists.choose = position :=
        atPosition_unique parameter hexists.choose_spec hposition
      simp [hchosen]
  · constructor
    · simp
    · intro hposition
      exact (hexists ⟨position, hposition⟩).elim

inductive SplitHashKey where
  | ordinary (input : HashInput)
  | hidden (coordinate : Coordinate)
deriving DecidableEq

abbrev SplitHashCache := SplitHashKey → Option HashOutput

def emptySplitHashCache : SplitHashCache := fun _ => none

noncomputable def tableValue (table : Coordinate → HashOutput)
    (position : Position) : Digest :=
  truncateHash (table (.position position))

def IsOtsPosition : Position → Prop
  | .chain _ _ _ _ _ => True
  | .leaf _ _ _ => True
  | .node _ _ _ _ => True
  | _ => False

noncomputable def tableOtsSecret (table : Coordinate → HashOutput) :
    Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leafIdx chainIdx =>
    truncateHash (table (.chainStart lay tree leafIdx chainIdx))

noncomputable def tablePayload (table : Coordinate → HashOutput) :
    Position → HashInput
  | position@(.chain lay tree leafIdx chainIdx step) =>
      if step.val = 0 then
        digestBytes (truncateHash (table (.chainStart lay tree leafIdx chainIdx)))
      else
        (position.children.map (tableValue table)).flatMap digestBytes
  | position => (position.children.map (tableValue table)).flatMap digestBytes

noncomputable def tableInput (parameter : PublicParameter)
    (table : Coordinate → HashOutput) : Coordinate → HashInput
  | .chainStart _ _ _ _ => []
  | .position position =>
      tweakableHashInput parameter position.domain (tablePayload table position)

noncomputable def tableAnswerDecoded (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (input : HashInput) : Option Position → HashOutput
  | some position@(.chain _ _ _ _ _) =>
      if input = tableInput parameter table (.position position) then
        table (.position position)
      else fallback input
  | some position@(.leaf _ _ _) =>
      if input = tableInput parameter table (.position position) then
        table (.position position)
      else fallback input
  | some position@(.node _ _ _ _) =>
      if input = tableInput parameter table (.position position) then
        table (.position position)
      else fallback input
  | _ => fallback input

noncomputable def tableAnswer (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id) :
    QueryImpl HashSpec Id :=
  fun input => tableAnswerDecoded parameter table fallback input
    (decodePosition? parameter input)

noncomputable def completedSplitHashCache (table : Coordinate → HashOutput)
    (ensured : Finset Coordinate) (cache : SplitHashCache) : SplitHashCache
  | .ordinary input => cache (.ordinary input)
  | .hidden coordinate =>
      match cache (.hidden coordinate) with
      | some output => some output
      | none => if coordinate ∈ ensured then some (table coordinate) else none

noncomputable def mergeDecodedPosition (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache) (input : HashInput) : Option Position → Option HashOutput
  | some position@(.chain _ _ _ _ _) =>
      if input = tableInput parameter table (.position position) then
        completedSplitHashCache table ensured cache (.hidden (.position position))
      else cache (.ordinary input)
  | some position@(.leaf _ _ _) =>
      if input = tableInput parameter table (.position position) then
        completedSplitHashCache table ensured cache (.hidden (.position position))
      else cache (.ordinary input)
  | some position@(.node _ _ _ _) =>
      if input = tableInput parameter table (.position position) then
        completedSplitHashCache table ensured cache (.hidden (.position position))
      else cache (.ordinary input)
  | _ => cache (.ordinary input)

noncomputable def mergedCache (parameter : PublicParameter)
    (table : Coordinate → HashOutput) (ensured : Finset Coordinate)
    (cache : SplitHashCache) : QueryCache HashSpec :=
  fun input => mergeDecodedPosition parameter table ensured cache input
    (decodePosition? parameter input)

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

noncomputable def ordinaryRomImpl :
    QueryImpl OracleWorld
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  splitUniformImpl + ordinaryHashImpl

noncomputable def ensureCoordinate (coordinate : Coordinate) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit :=
  liftM (LazyRevealProbe.ensureQuery coordinate)

noncomputable def revealCoordinateOutput (coordinate : Coordinate) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  let output ← liftM (LazyRevealProbe.revealQuery coordinate)
  modify fun cache : SplitHashCache =>
    Function.update cache (.hidden coordinate) (some output)
  pure output

noncomputable def revealCoordinate (coordinate : Coordinate) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest := do
  let output ← revealCoordinateOutput coordinate
  pure (truncateHash output)

noncomputable def publishCoordinate (coordinate : Coordinate) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit :=
  liftM (LazyRevealProbe.publishQuery coordinate)

noncomputable def revealPosition (position : Position) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest :=
  revealCoordinate (.position position)

noncomputable def revealChainStart (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest :=
  revealCoordinate (.chainStart lay tree leafIdx chainIdx)

theorem revealCoordinate_run (coordinate : Coordinate) (cache : SplitHashCache) :
    (revealCoordinate coordinate).run cache = (do
      let output ← LazyRevealProbe.revealQuery coordinate
      pure (truncateHash output,
        Function.update cache (.hidden coordinate) (some output))) := by
  simp [revealCoordinate, revealCoordinateOutput, StateT.run_modify]

theorem revealPosition_run (position : Position) (cache : SplitHashCache) :
    (revealPosition position).run cache = (do
      let output ← LazyRevealProbe.revealQuery (.position position)
      pure (truncateHash output,
        Function.update cache (.hidden (.position position)) (some output))) := by
  rw [revealPosition, revealCoordinate_run]

noncomputable def peekCoordinate (coordinate : Coordinate) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Digest) := do
  let output ← liftM (LazyRevealProbe.peekQuery coordinate)
  pure (truncateHash <$> output)

noncomputable def peekPositionValues : List Position →
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option (List Digest))
  | [] => pure (some [])
  | position :: remaining => do
      match ← peekCoordinate (.position position) with
      | none => pure none
      | some value =>
          match ← peekPositionValues remaining with
          | none => pure none
          | some values => pure (some (value :: values))

noncomputable def peekTableInput (parameter : PublicParameter) : Coordinate →
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option HashInput)
  | .chainStart _ _ _ _ => pure none
  | .position position@(.chain lay tree leafIdx chainIdx step) => do
      if step.val = 0 then
        match ← peekCoordinate (.chainStart lay tree leafIdx chainIdx) with
        | none => pure none
        | some value =>
            pure (some (tweakableHashInput parameter position.domain (digestBytes value)))
      else
        match ← peekPositionValues position.children with
        | none => pure none
        | some values =>
            pure (some (tweakableHashInput parameter position.domain
              (values.flatMap digestBytes)))
  | .position position => do
      match ← peekPositionValues position.children with
      | none => pure none
      | some values =>
          pure (some (tweakableHashInput parameter position.domain
            (values.flatMap digestBytes)))

noncomputable def ensureFullChain (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit := do
  let _ ← sequenceFin fun step : ChainStep =>
    ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))
  pure ()

noncomputable def ensureChainPrefix (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit := do
  let _ ← sequenceFin fun step : ChainStep =>
    if step.val < digit.val then
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))
    else
      pure ()
  pure ()

noncomputable def ensureOtsLeaf (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit := do
  let _ ← sequenceFin fun chainIdx : ChainIndex =>
    ensureFullChain lay tree leafIdx chainIdx
  ensureCoordinate (.position (.leaf lay tree leafIdx))

noncomputable def ensureTreeNode (lay : Layer) (tree : TreeIndex) :
    Nat → Nat →
      StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit
  | 0, nodeIdx => ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => do
      ensureTreeNode lay tree level (2 * nodeIdx)
      ensureTreeNode lay tree level (2 * nodeIdx + 1)
      if hlevel : level < maxLayerHeight then
        ensureCoordinate (.position
          (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
      else
        pure ()

noncomputable def maskedTreeNode (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest := do
  ensureTreeNode lay tree level nodeIdx
  match level with
  | 0 => revealPosition (.leaf lay tree (leafOfNat nodeIdx))
  | current + 1 =>
      if hlevel : current < maxLayerHeight then
        revealPosition (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx))
      else
        pure 0

noncomputable def maskedTreeRoot (lay : Layer) (tree : TreeIndex) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest :=
  maskedTreeNode lay tree (layerHeight lay) 0

noncomputable def maskedTreePath (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate))
        (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      maskedTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    else
      pure 0

noncomputable def ensureTreePath (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit := do
  let _ ← sequenceFin fun level : Fin maxLayerHeight =>
    if level.val < layerHeight lay then
      ensureTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    else
      pure ()
  pure ()

noncomputable def maskedChainValue (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest := do
  ensureChainPrefix lay tree leafIdx chainIdx digit
  if hzero : digit.val = 0 then
    revealChainStart lay tree leafIdx chainIdx
  else
    let step : ChainStep := ⟨digit.val - 1, by
      have := digit.isLt
      omega⟩
    revealPosition (.chain lay tree leafIdx chainIdx step)

noncomputable def maskedOtsSignFrom (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    Nat → Nat →
      StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))
          (Option (Counter × (ChainIndex → Digit)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      let encoded ← simulateQ ordinaryHashImpl
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))
      match encoded with
      | some encoding => do
          let _ ← sequenceFin fun chainIdx =>
            ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx)
          pure (some (BitVec.ofNat counterBits counter, encoding))
      | none =>
          maskedOtsSignFrom parameter lay tree leafIdx message attempts (counter + 1)

noncomputable def maskedOtsSign (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate))
        (Option (Counter × (ChainIndex → Digit))) :=
  maskedOtsSignFrom parameter lay tree leafIdx message encodingAttemptLimit 0

noncomputable def maskedLayerMessage (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    maskedTreeRoot below (treeIndexAt index below)
  else
    simulateQ ordinaryHashImpl (ftsKey parameter index (ftsSecret index))

noncomputable def maskedSignLayer (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate))
        (Option (Counter × (ChainIndex → Digit))) := do
  let tree := treeIndexAt index lay
  let leafIdx := leafIndexAt index lay
  let message ← maskedLayerMessage parameter ftsSecret index lay
  match ← maskedOtsSign parameter lay tree leafIdx message with
  | none => pure none
  | some (counter, encoding) => do
      ensureTreePath lay tree leafIdx
      pure (some (counter, encoding))

noncomputable def chainValueCoordinate (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit) : Coordinate :=
  if hzero : digit.val = 0 then
    .chainStart lay tree leafIdx chainIdx
  else
    .position (.chain lay tree leafIdx chainIdx ⟨digit.val - 1, by
      have := digit.isLt
      omega⟩)

@[simp] theorem toProbe_coordinate (probe : OtsValueProbe) :
    (toProbe probe).coordinate =
      chainValueCoordinate probe.lay probe.tree probe.leafIdx probe.chainIdx probe.digit := by
  unfold toProbe chainValueCoordinate
  split_ifs <;> rfl

theorem chainValueCoordinate_injective
    {leftLay rightLay : Layer} {leftTree rightTree : TreeIndex}
    {leftLeaf rightLeaf : LeafIndex} {leftChain rightChain : ChainIndex}
    {leftDigit rightDigit : Digit}
    (heq : chainValueCoordinate leftLay leftTree leftLeaf leftChain leftDigit =
      chainValueCoordinate rightLay rightTree rightLeaf rightChain rightDigit) :
    leftLay = rightLay ∧ leftTree = rightTree ∧ leftLeaf = rightLeaf ∧
      leftChain = rightChain ∧ leftDigit = rightDigit := by
  by_cases hleft : leftDigit.val = 0
  · by_cases hright : rightDigit.val = 0
    · simp only [chainValueCoordinate, hleft, hright, ↓reduceDIte,
        Coordinate.chainStart.injEq] at heq
      exact ⟨heq.1, heq.2.1, heq.2.2.1, heq.2.2.2,
        Fin.ext (hleft.trans hright.symm)⟩
    · simp [chainValueCoordinate, hleft, hright] at heq
  · by_cases hright : rightDigit.val = 0
    · simp [chainValueCoordinate, hleft, hright] at heq
    · simp only [chainValueCoordinate, hleft, hright, ↓reduceDIte,
        Coordinate.position.injEq, Position.chain.injEq] at heq
      refine ⟨heq.1, heq.2.1, heq.2.2.1, heq.2.2.2.1, Fin.ext ?_⟩
      have hleftLt := leftDigit.isLt
      have hrightLt := rightDigit.isLt
      have hleftPos : 0 < leftDigit.val := Nat.pos_of_ne_zero hleft
      have hrightPos : 0 < rightDigit.val := Nat.pos_of_ne_zero hright
      have hsub : leftDigit.val - 1 = rightDigit.val - 1 := by
        simpa using congrArg Fin.val heq.2.2.2.2
      omega

noncomputable def revealPublishedCoordinate (coordinate : Coordinate) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Digest := do
  let value ← revealCoordinate coordinate
  publishCoordinate coordinate
  pure value

noncomputable def revealLayerValues (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate))
        ((ChainIndex → Digest) × (Fin maxLayerHeight → Digest)) := do
  let tree := treeIndexAt index lay
  let leafIdx := leafIndexAt index lay
  let values ← sequenceFin fun chainIdx =>
    revealPublishedCoordinate
      (chainValueCoordinate lay tree leafIdx chainIdx (encoding chainIdx))
  let path ← sequenceFin fun level : Fin maxLayerHeight =>
    if level.val < layerHeight lay then
      match level.val with
      | 0 => revealPublishedCoordinate (.position (.leaf lay tree
          (leafOfNat (Nat.xor leafIdx.val 1))))
      | current + 1 =>
          if hlevel : current < maxLayerHeight then
            revealPublishedCoordinate (.position (.node lay tree ⟨current, hlevel⟩
              (leafOfNat (Nat.xor (leafIdx.val / 2 ^ (current + 1)) 1))))
          else pure 0
    else pure 0
  pure (values, path)

noncomputable def maskedSignAfterDigest (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature) := do
  let ftsPath ← simulateQ ordinaryHashImpl
    (ftsOpen parameter index leaves (ftsSecret index))
  let layers ← sequenceFin fun lay =>
    maskedSignLayer parameter ftsSecret index lay
  match traverseOption layers with
  | none => pure none
  | some parts =>
      let revealed ← sequenceFin fun lay => revealLayerValues index lay (parts lay).2
      pure (some
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 })

noncomputable def maskedSign (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature) := do
  let secretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  match ← simulateQ ordinaryRomImpl
      (signDigestLoop digestAttemptLimit secretKey message) with
  | none => pure none
  | some (randomness, index, leaves) =>
      maskedSignAfterDigest parameter ftsSecret randomness index leaves

noncomputable def probe (candidate : Probe) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit :=
  liftM (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate)

noncomputable def probeFirstMissingInputCoordinate (input : HashInput) :
    Nat → List Coordinate →
      StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit
  | _, [] => pure ()
  | slot, coordinate :: remaining => do
      match ← peekCoordinate coordinate with
      | none => probe ⟨coordinate, slotDigest slot input⟩
      | some _ => probeFirstMissingInputCoordinate input (slot + 1) remaining

noncomputable def resolveKnownInput (parameter : PublicParameter)
    (coordinate : Coordinate) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  match ← peekTableInput parameter coordinate with
  | some knownInput =>
      if knownInput = input then
        let output ← revealCoordinateOutput coordinate
        publishCoordinate coordinate
        modify fun cache : SplitHashCache =>
          Function.update cache (.ordinary input) (some output)
        pure output
      else
        splitHashQuery (.ordinary input)
  | none => splitHashQuery (.ordinary input)

noncomputable def prepareLeafInputProbe (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit := do
  match ← peekCoordinate candidate.coordinate with
  | none => probe candidate
  | some _ =>
      probeFirstMissingInputCoordinate input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

noncomputable def probingHashQuery (parameter : PublicParameter) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput :=
  match decodeProbe? parameter input with
  | some candidate =>
      match decodePosition? parameter input with
      | some (.leaf lay tree leafIdx) => do
          prepareLeafInputProbe input candidate lay tree leafIdx
          resolveKnownInput parameter candidate.outputCoordinate input
      | _ => do
          probe candidate
          resolveKnownInput parameter candidate.outputCoordinate input
  | none =>
      match decodePosition? parameter input with
      | some position@(.chain _ _ _ _ _) =>
          resolveKnownInput parameter (.position position) input
      | some position@(.leaf _ _ _) =>
          resolveKnownInput parameter (.position position) input
      | some position@(.node _ _ _ _) => do
          probeFirstMissingInputCoordinate input 0 (position.children.map .position)
          resolveKnownInput parameter (.position position) input
      | _ => splitHashQuery (.ordinary input)

noncomputable def probingHashImpl (parameter : PublicParameter) :
    QueryImpl HashSpec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  fun input => probingHashQuery parameter input

noncomputable def probingRomImpl (parameter : PublicParameter) :
    QueryImpl OracleWorld
      (StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate))) :=
  splitUniformImpl + probingHashImpl parameter

noncomputable def revealPositionValues : List Position →
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (List Digest)
  | [] => pure []
  | position :: remaining => do
      let value ← revealPosition position
      let values ← revealPositionValues remaining
      pure (value :: values)

noncomputable def revealTableInputChildren : Coordinate →
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Unit
  | .chainStart _ _ _ _ => pure ()
  | .position position@(.chain lay tree leafIdx chainIdx step) => do
      if step.val = 0 then
        let _ ← revealChainStart lay tree leafIdx chainIdx
        pure ()
      else
        let _ ← revealPositionValues position.children
        pure ()
  | .position position => do
      let _ ← revealPositionValues position.children
      pure ()

noncomputable def resolveVerifierInput (parameter : PublicParameter)
    (coordinate : Coordinate) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  let cache ← get
  match cache (.ordinary input) with
  | some output => pure output
  | none =>
      revealTableInputChildren coordinate
      resolveKnownInput parameter coordinate input

noncomputable def verifierHashQuery (parameter : PublicParameter) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  match decodeProbe? parameter input with
  | some candidate => do
      probe candidate
      resolveVerifierInput parameter candidate.outputCoordinate input
  | none =>
      match decodePosition? parameter input with
      | some position@(.chain _ _ _ _ _) =>
          resolveVerifierInput parameter (.position position) input
      | some position@(.leaf _ _ _) =>
          resolveVerifierInput parameter (.position position) input
      | some position@(.node _ _ _ _) =>
          resolveVerifierInput parameter (.position position) input
      | _ => splitHashQuery (.ordinary input)

noncomputable def verifierHashImpl (parameter : PublicParameter) :
    QueryImpl HashSpec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  fun input => verifierHashQuery parameter input

noncomputable def verifierRomImpl (parameter : PublicParameter) :
    QueryImpl OracleWorld
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  splitUniformImpl + verifierHashImpl parameter

noncomputable def maskedSigningImpl (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    QueryImpl SigningSpec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  fun message => maskedSign parameter root ftsSecret message

noncomputable def maskedExpandedAdversaryImpl (parameter : PublicParameter)
    (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))) :=
  probingRomImpl parameter + maskedSigningImpl parameter root ftsSecret

abbrev RetainedRestResult := (Forgery × QueryLog SigningSpec) × Bool

abbrev RetainedGameResult := Digest × RetainedRestResult

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
  | pure value => simp [signingTraceComputation]
  | query_bind input next ih => simp [signingTraceComputation, ih]

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

noncomputable def retainedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) RetainedRestResult := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure ((forgery, log), verified)

theorem simulateQ_maskedExpanded_retainedGameRestComputation
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
        (retainedGameRestComputation adversary ⟨root, parameter⟩) = (do
      let (forgery, log) ←
        simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
          (signingTraceComputation (adversary.main ⟨root, parameter⟩))
      let verified ← simulateQ (probingRomImpl parameter)
        (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
      pure ((forgery, log), verified)) := by
  unfold retainedGameRestComputation
  rw [simulateQ_bind]
  apply bind_congr
  intro result
  rcases result with ⟨forgery, log⟩
  rw [simulateQ_bind]
  change (do
    let verified ← simulateQ
      (probingRomImpl parameter + maskedSigningImpl parameter root ftsSecret)
      (liftOracleWorldLeft
        (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature))
    pure ((forgery, log), verified)) = _
  rw [simulateQ_liftOracleWorldLeft]

noncomputable def maskedRetainedGameAfterFtsSecrets (adversary : Adversary)
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) RetainedGameResult := do
  let root ← maskedTreeRoot topLayer rootTree
  publishCoordinate (.position (.node topLayer rootTree
    ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))
  let (forgery, log) ←
    simulateQ (maskedExpandedAdversaryImpl parameter root ftsSecret)
      (signingTraceComputation (adversary.main ⟨root, parameter⟩))
  let verified ← simulateQ (verifierRomImpl parameter)
    (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
  pure (root, ((forgery, log), verified))

noncomputable def maskedGameAfterFtsSecrets (adversary : Adversary)
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) Bool := do
  let root ← maskedTreeRoot topLayer rootTree
  publishCoordinate (.position (.node topLayer rootTree
    ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))
  let (forgery, log) ←
    (simulateQ (QueryImpl.withTraceAppend
      (maskedExpandedAdversaryImpl parameter root ftsSecret) signingLogFragment)
      (adversary.main ⟨root, parameter⟩)).run
  let verified ← simulateQ (verifierRomImpl parameter)
    (scheme.verify ⟨root, parameter⟩ forgery.message forgery.signature)
  pure (decide (SigningTranscript.Valid log ∧
    ¬SigningTranscript.Contains log forgery) && verified)

end SphincsSecurity.Concrete.OtsProbeSimulation
