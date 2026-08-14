import XmssSecurity.ChainEdgeHighUniformity
import XmssSecurity.CausalKeygenCoupling
import XmssSecurity.CausalHighTableKeygen
import XmssSecurity.MarginalCoupling
import VCVio.ProgramLogic.Relational.Basic

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def cachedHashOutputHigh (cache : QueryCache HashSpec)
    (input : HashInput) : Digest :=
  match cache input with
  | none => 0
  | some output => hashOutputHigh output

theorem cachedHashOutputHigh_cacheQuery_of_ne
    (cache : QueryCache HashSpec) (input candidate : HashInput)
    (output : HashOutput) (hne : candidate ≠ input) :
    cachedHashOutputHigh (cache.cacheQuery input output) candidate =
      cachedHashOutputHigh cache candidate := by
  simp [cachedHashOutputHigh, QueryCache.cacheQuery_of_ne, hne]

noncomputable def programmedChainExtensionWithHigh
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    ProbComp ((Vector Digest ((n + 1) + 1) × QueryCache HashSpec) × Digest) := do
  let low ← $ᵗ Digest
  let high ← $ᵗ Digest
  let input := Concrete.CacheView.chainInput parameter epoch chain step values.back
  let output := Rom.hashOutputEquivDigestPair.symm (high, low)
  pure ((values.push low, cache.cacheQuery input output), high)

theorem evalDist_programmedChainExtension_exposes_independent_high
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    evalDist ((fun result =>
      (result, cachedHashOutputHigh result.2
        (Concrete.CacheView.chainInput parameter epoch chain step values.back))) <$>
          programmedChainExtension parameter epoch chain step values cache) =
    evalDist (programmedChainExtensionWithHigh parameter epoch chain step values cache) := by
  unfold programmedChainExtension programmedChainExtensionWithHigh
    Rom.sampledHashOutputWithDigest Rom.sampleHashOutputWithDigest
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro low
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro high
  simp [cachedHashOutputHigh, hashOutputHigh]

def ProgrammedChainExtensionHighRelation
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec)
    (left : Vector Digest ((n + 1) + 1) × QueryCache HashSpec)
    (right : (Vector Digest ((n + 1) + 1) × QueryCache HashSpec) × Digest) : Prop :=
  left = right.1 ∧
    cachedHashOutputHigh left.2
      (Concrete.CacheView.chainInput parameter epoch chain step values.back) =
        right.2 ∧
    ∃ low,
      left.1 = values.push low ∧
      left.2 = cache.cacheQuery
        (Concrete.CacheView.chainInput parameter epoch chain step values.back)
        (Rom.hashOutputEquivDigestPair.symm (right.2, low))

theorem programmedChainExtensionWithHigh_support_info
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec)
    (result : (Vector Digest ((n + 1) + 1) × QueryCache HashSpec) × Digest)
    (hresult : result ∈ support
      (programmedChainExtensionWithHigh parameter epoch chain step values cache)) :
    ∃ low,
      result.1.1 = values.push low ∧
      result.1.2 = cache.cacheQuery
        (Concrete.CacheView.chainInput parameter epoch chain step values.back)
        (Rom.hashOutputEquivDigestPair.symm (result.2, low)) := by
  unfold programmedChainExtensionWithHigh at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨low, _hlow, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨high, _hhigh, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact ⟨low, rfl, rfl⟩

theorem relTriple_programmedChainExtension_exposes_independent_high
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    RelTriple
      (programmedChainExtension parameter epoch chain step values cache)
      (programmedChainExtensionWithHigh parameter epoch chain step values cache)
      (ProgrammedChainExtensionHighRelation parameter epoch chain step values cache) := by
  classical
  let expose := fun result :
      Vector Digest ((n + 1) + 1) × QueryCache HashSpec =>
    (result, cachedHashOutputHigh result.2
      (Concrete.CacheView.chainInput parameter epoch chain step values.back))
  apply relTriple_post_mono
    (relTriple_of_evalDist_map_eq_with_support_general
      (programmedChainExtension parameter epoch chain step values cache)
      (programmedChainExtensionWithHigh parameter epoch chain step values cache)
      expose id (by
        simpa [expose] using
          (evalDist_programmedChainExtension_exposes_independent_high
            parameter epoch chain step values cache)))
  intro left right hrelation
  have heq : expose left = right := by simpa using hrelation.1
  have hleft : left = right.1 := congrArg Prod.fst heq
  refine ⟨hleft, congrArg Prod.snd heq, ?_⟩
  rw [hleft]
  exact programmedChainExtensionWithHigh_support_info
    parameter epoch chain step values cache right hrelation.2.2

noncomputable def programmedSingleChainEdgeHalvesView
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) (hvalid : position < chainLength - 1)
    (value : Digest) (cache : QueryCache HashSpec) :
    ProbComp (Digest × Digest) :=
  (fun result =>
    (result.1.back,
      cachedHashOutputHigh result.2
        (Concrete.CacheView.chainInput parameter epoch chain
          ⟨position, hvalid⟩ value))) <$>
    programmedSingleChainEdge parameter epoch chain position hvalid value cache

theorem evalDist_programmedSingleChainEdge_halves_independent
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) (hvalid : position < chainLength - 1)
    (value : Digest) (cache : QueryCache HashSpec) :
    evalDist (programmedSingleChainEdgeHalvesView parameter epoch chain
      position hvalid value cache) =
    evalDist (do
      let low ← $ᵗ Digest
      let high ← $ᵗ Digest
      pure (low, high)) := by
  unfold programmedSingleChainEdgeHalvesView programmedSingleChainEdge
    Rom.sampledHashOutputWithDigest Rom.sampleHashOutputWithDigest
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro low
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro high
  simp [cachedHashOutputHigh, hashOutputHigh]

noncomputable def programmedChainTrajectoryWithHigh :
    (parameter : PublicParameter) → (epoch : Epoch) → (chain : ChainIndex) →
    (position : Nat) → (steps : Nat) → Digest → QueryCache HashSpec →
      ProbComp ((Vector Digest (steps + 1) × QueryCache HashSpec) ×
        (Fin steps → Digest))
  | _parameter, _epoch, _chain, _position, 0, value, cache =>
      pure ((Vector.ofFn (fun _ => value), cache), fun index => Fin.elim0 index)
  | parameter, epoch, chain, position, steps + 1, value, cache => do
      let prior ← programmedChainTrajectoryWithHigh parameter epoch chain position
        steps value cache
      if hvalid : position + steps < chainLength - 1 then
        let extended ← programmedChainExtensionWithHigh parameter epoch chain
          ⟨position + steps, hvalid⟩ prior.1.1 prior.1.2
        pure (extended.1, Fin.lastCases extended.2 prior.2)
      else
        pure ((prior.1.1.push 0, prior.1.2), Fin.lastCases 0 prior.2)

def ProgrammedChainTrajectoryHighRelation
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (hbound : position + steps ≤ chainLength - 1)
    (initialCache : QueryCache HashSpec)
    (left : Vector Digest (steps + 1) × QueryCache HashSpec)
    (right : (Vector Digest (steps + 1) × QueryCache HashSpec) ×
      (Fin steps → Digest)) : Prop :=
  left = right.1 ∧
    (∀ input,
      (∀ step value,
        input ≠ Concrete.CacheView.chainInput parameter epoch chain step value) →
      left.2 input = initialCache input) ∧
    (∀ offset : Fin steps,
      cachedHashOutputHigh left.2
        (Concrete.CacheView.chainInput parameter epoch chain
          ⟨position + offset.val, by omega⟩
          (left.1.get ⟨offset.val, by omega⟩)) = right.2 offset)

set_option maxRecDepth 100000 in
theorem relTriple_programmedChainTrajectory_exposes_independent_high
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec)
      (hbound : position + steps ≤ chainLength - 1),
    RelTriple
      (programmedChainTrajectory parameter epoch chain position steps value cache)
      (programmedChainTrajectoryWithHigh parameter epoch chain position steps
        value cache)
      (ProgrammedChainTrajectoryHighRelation parameter epoch chain position steps
        hbound cache) := by
  intro steps
  induction steps with
  | zero =>
      intro value cache hbound
      apply relTriple_pure_pure
      exact ⟨rfl, fun _input _hinput => rfl,
        fun offset => Fin.elim0 offset⟩
  | succ steps ih =>
      intro value cache hbound
      have hvalid : position + steps < chainLength - 1 := by omega
      rw [programmedChainTrajectory, programmedChainTrajectoryWithHigh]
      simp only [hvalid, ↓reduceDIte]
      apply relTriple_bind (ih value cache (by omega))
      intro leftPrior rightPrior hprior
      rw [hprior.1]
      apply relTriple_bind
        (relTriple_programmedChainExtension_exposes_independent_high
          parameter epoch chain ⟨position + steps, hvalid⟩
            rightPrior.1.1 rightPrior.1.2)
      intro leftExtended rightExtended hextended
      apply relTriple_pure_pure
      obtain ⟨low, hvalues, hcache⟩ := hextended.2.2
      refine ⟨by simpa using hextended.1, ?_, ?_⟩
      · intro input hinput
        rw [hcache, QueryCache.cacheQuery_of_ne]
        · simpa [hprior.1] using hprior.2.1 input hinput
        · exact hinput ⟨position + steps, hvalid⟩ rightPrior.1.1.back
      intro offset
      cases offset using Fin.lastCases with
      | last =>
          have hvalueAt : leftExtended.1.get ⟨steps, by omega⟩ =
              rightPrior.1.1.back := by
            rw [hvalues]
            change (rightPrior.1.1.push low)[steps] = rightPrior.1.1.back
            rw [Vector.getElem_push_lt (by omega), Vector.back_eq_getElem]
            simp
          simpa [hvalueAt] using hextended.2.1
      | cast offset =>
          have hvalueAt : leftExtended.1.get
                ⟨offset.castSucc.val, by omega⟩ =
              rightPrior.1.1.get ⟨offset.val, by omega⟩ := by
            rw [hvalues]
            change (rightPrior.1.1.push low)[offset.val] =
              rightPrior.1.1[offset.val]
            rw [Vector.getElem_push_lt (by omega)]
          simp only [Fin.lastCases_castSucc]
          rw [hcache]
          rw [hvalueAt]
          simp only [Fin.val_castSucc]
          have hoffset : offset.val < steps := offset.isLt
          have hne : Concrete.CacheView.chainInput parameter epoch chain
                ⟨position + offset.val, by omega⟩
                (rightPrior.1.1.get ⟨offset.val, by omega⟩) ≠
              Concrete.CacheView.chainInput parameter epoch chain
                ⟨position + steps, hvalid⟩ rightPrior.1.1.back := by
            intro heq
            have hparts := (Concrete.CacheView.chainInput_eq_iff parameter
              epoch epoch chain chain
                ⟨position + offset.val, by omega⟩
                ⟨position + steps, hvalid⟩
                (rightPrior.1.1.get ⟨offset.val, by omega⟩)
                rightPrior.1.1.back).mp heq
            have hstep := congrArg Fin.val hparts.2.2.1
            simp only at hstep
            omega
          rw [cachedHashOutputHigh_cacheQuery_of_ne _ _ _ _ hne]
          have hpriorHigh := hprior.2.2 offset
          rw [hprior.1] at hpriorHigh
          simpa using hpriorHigh

noncomputable def programmedFixedSeedChainTrajectoriesWithHigh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) : QueryCache HashSpec → List Epoch →
      ProbComp ((List (Vector Digest (steps + 1)) × QueryCache HashSpec) ×
        List (Fin steps → Digest))
  | cache, [] => pure (([], cache), [])
  | cache, epoch :: epochs => do
      let first ← programmedChainTrajectoryWithHigh parameter epoch chain 0
        steps (secret epoch chain) cache
      let rest ← programmedFixedSeedChainTrajectoriesWithHigh parameter secret
        chain steps first.1.2 epochs
      pure ((first.1.1 :: rest.1.1, rest.1.2), first.2 :: rest.2)

def ChainTrajectoryHighRowsMatch
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) (cache : QueryCache HashSpec) :
    List Epoch → List (Vector Digest (steps + 1)) →
      List (Fin steps → Digest) → Prop
  | [], [], [] => True
  | epoch :: epochs, trajectory :: trajectories, high :: highs =>
      (∀ offset : Fin steps,
        cachedHashOutputHigh cache
          (Concrete.CacheView.chainInput parameter epoch chain
            ⟨offset.val, by omega⟩
            (trajectory.get ⟨offset.val, by omega⟩)) = high offset) ∧
      ChainTrajectoryHighRowsMatch parameter chain steps hsteps cache
        epochs trajectories highs
  | _, _, _ => False

def ProgrammedFixedSeedTrajectoriesHighRelation
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) (epochs : List Epoch)
    (initialCache : QueryCache HashSpec)
    (left : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
    (right : (List (Vector Digest (steps + 1)) × QueryCache HashSpec) ×
      List (Fin steps → Digest)) : Prop :=
  left = right.1 ∧
    (∀ input,
      (∀ epoch ∈ epochs, ∀ step value,
        input ≠ Concrete.CacheView.chainInput parameter epoch chain step value) →
      left.2 input = initialCache input) ∧
    ChainTrajectoryHighRowsMatch parameter chain steps hsteps left.2
      epochs left.1 right.2

set_option maxRecDepth 100000 in
theorem relTriple_programmedFixedSeedChainTrajectories_exposes_high
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec), epochs.Nodup →
    RelTriple
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        steps cache epochs)
      (programmedFixedSeedChainTrajectoriesWithHigh parameter secret chain
        steps cache epochs)
      (ProgrammedFixedSeedTrajectoriesHighRelation parameter chain steps hsteps
        epochs cache) := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache _hnodup
      apply relTriple_pure_pure
      exact ⟨rfl, fun _input _hinput => rfl, trivial⟩
  | cons epoch epochs ih =>
      intro cache hnodup
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [programmedFixedSeedChainTrajectoriesFromCache_cons,
        programmedFixedSeedChainTrajectoriesWithHigh]
      apply relTriple_bind
        (relTriple_programmedChainTrajectory_exposes_independent_high
          parameter epoch chain 0 steps (secret epoch chain) cache (by omega))
      intro leftFirst rightFirst hfirst
      rcases hfirst with ⟨hfirstEq, hfirstPreserved, hfirstHigh⟩
      subst leftFirst
      apply relTriple_bind (ih rightFirst.1.2 htailNodup)
      intro leftRest rightRest hrest
      rcases hrest with ⟨hrestEq, hrestPreserved, hrestRows⟩
      subst leftRest
      apply relTriple_pure_pure
      refine ⟨rfl, ?_, ?_⟩
      · intro input hinput
        calc
          rightRest.1.2 input = rightFirst.1.2 input := by
            simpa using hrestPreserved input (by
              intro later hlater step value
              exact hinput later (by simp [hlater]) step value)
          _ = cache input := by
            simpa using hfirstPreserved input (by
              intro step value
              exact hinput epoch (by simp) step value)
      · change
          (∀ offset : Fin steps,
            cachedHashOutputHigh rightRest.1.2
              (Concrete.CacheView.chainInput parameter epoch chain
                ⟨offset.val, by omega⟩
                (rightFirst.1.1.get ⟨offset.val, by omega⟩)) =
              rightFirst.2 offset) ∧
          ChainTrajectoryHighRowsMatch parameter chain steps hsteps
            rightRest.1.2 epochs rightRest.1.1 rightRest.2
        constructor
        · intro offset
          let input := Concrete.CacheView.chainInput parameter epoch chain
            ⟨offset.val, by omega⟩
            (rightFirst.1.1.get ⟨offset.val, by omega⟩)
          let firstInput := Concrete.CacheView.chainInput parameter epoch chain
            ⟨0 + offset.val, by omega⟩
            (rightFirst.1.1.get ⟨offset.val, by omega⟩)
          have hinputEq : firstInput = input := by
            apply congrArg (fun step => Concrete.CacheView.chainInput parameter
              epoch chain step (rightFirst.1.1.get ⟨offset.val, by omega⟩))
            apply Fin.ext
            simp
          have hpreserved : rightRest.1.2 input = rightFirst.1.2 input := by
            simpa using hrestPreserved input (by
              intro later hlater step value heq
              have hparts := (Concrete.CacheView.chainInput_eq_iff parameter
                epoch later chain chain ⟨offset.val, by omega⟩ step
                  (rightFirst.1.1.get ⟨offset.val, by omega⟩) value).mp heq
              exact hnotMem (hparts.1 ▸ hlater))
          change cachedHashOutputHigh rightRest.1.2 input = rightFirst.2 offset
          rw [cachedHashOutputHigh, hpreserved, ← hinputEq]
          exact hfirstHigh offset
        · exact hrestRows

theorem ChainTrajectoryHighRowsMatch.lengths
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) (cache : QueryCache HashSpec) :
    ∀ epochs trajectories highs,
      ChainTrajectoryHighRowsMatch parameter chain steps hsteps cache
        epochs trajectories highs →
      epochs.length = trajectories.length ∧ epochs.length = highs.length := by
  intro epochs
  induction epochs with
  | nil =>
      intro trajectories highs hmatch
      cases trajectories <;> cases highs <;>
        simp [ChainTrajectoryHighRowsMatch] at hmatch ⊢
  | cons epoch epochs ih =>
      intro trajectories highs hmatch
      cases trajectories with
      | nil => simp [ChainTrajectoryHighRowsMatch] at hmatch
      | cons trajectory trajectories =>
          cases highs with
          | nil => simp [ChainTrajectoryHighRowsMatch] at hmatch
          | cons high highs =>
              obtain ⟨_hfirst, hrest⟩ := hmatch
              obtain ⟨htrajectories, hhighs⟩ :=
                ih trajectories highs hrest
              exact ⟨by simp [htrajectories], by simp [hhighs]⟩

theorem ChainTrajectoryHighRowsMatch.getElem
    (parameter : PublicParameter) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) (cache : QueryCache HashSpec) :
    ∀ epochs trajectories highs,
      ChainTrajectoryHighRowsMatch parameter chain steps hsteps cache
        epochs trajectories highs →
      ∀ (index : Nat) (hepoch : index < epochs.length)
        (htrajectory : index < trajectories.length)
        (hhigh : index < highs.length) (offset : Fin steps),
        cachedHashOutputHigh cache
          (Concrete.CacheView.chainInput parameter epochs[index] chain
            ⟨offset.val, by omega⟩
            (trajectories[index].get ⟨offset.val, by omega⟩)) =
          highs[index] offset := by
  intro epochs
  induction epochs with
  | nil =>
      intro trajectories highs hmatch index hepoch
      simp at hepoch
  | cons epoch epochs ih =>
      intro trajectories highs hmatch
      cases trajectories with
      | nil => simp [ChainTrajectoryHighRowsMatch] at hmatch
      | cons trajectory trajectories =>
          cases highs with
          | nil => simp [ChainTrajectoryHighRowsMatch] at hmatch
          | cons high highs =>
              obtain ⟨hfirst, hrest⟩ := hmatch
              intro index hepoch htrajectory hhigh offset
              cases index with
              | zero => simpa using hfirst offset
              | succ index =>
                  simpa using ih trajectories highs hrest index
                    (by simpa using hepoch) (by simpa using htrajectory)
                    (by simpa using hhigh) offset

noncomputable def chainEdgeHighTableOfRows
    (rows : List (ChainStep → Digest)) : ChainEdgeIndex → Digest := fun edge =>
  if hlength : allEpochs.length = rows.length then
    (rows[(epochPosition edge.1).val]'(by
      have hposition := (epochPosition edge.1).isLt
      omega)) edge.2
  else
    0

set_option maxRecDepth 100000 in
theorem chainEdgeHighTableOfCache_eq_rows
    (parameter : PublicParameter) (chain : ChainIndex)
    (trajectories : List FullChainTrajectory)
    (cache : QueryCache HashSpec) (rows : List (ChainStep → Digest))
    (hmatch : ChainTrajectoryHighRowsMatch parameter chain
      (chainLength - 1) le_rfl cache allEpochs trajectories rows) :
    chainEdgeHighTableOfCache cache parameter chain
      (chainValueTableOfList trajectories) = chainEdgeHighTableOfRows rows := by
  have hlengths := hmatch.lengths
  funext edge
  let position := epochPosition edge.1
  have htrajectory : position.val < trajectories.length := by
    rw [← hlengths.1]
    exact position.isLt
  have hhigh : position.val < rows.length := by
    rw [← hlengths.2]
    exact position.isLt
  have hrow := ChainTrajectoryHighRowsMatch.getElem parameter chain
    (chainLength - 1) le_rfl cache allEpochs trajectories rows hmatch
      position.val position.isLt htrajectory hhigh edge.2
  have hepoch : allEpochs[position.val] = edge.1 :=
    allEpochs_get_epochPosition edge.1
  rw [hepoch] at hrow
  have hrow' : cachedHashOutputHigh cache
      (Concrete.CacheView.chainInput parameter edge.1 chain edge.2
        (trajectories[(epochPosition edge.1).val].get
          ⟨edge.2.val, by omega⟩)) =
      rows[(epochPosition edge.1).val] edge.2 := by
    convert hrow using 1
  have htableValue : chainValueTableOfList trajectories
      (edge.1, chainStepDigit edge.2) =
      trajectories[position.val].get ⟨edge.2.val, by omega⟩ := by
    unfold chainValueTableOfList
    rw [dif_pos hlengths.1]
    rfl
  unfold chainEdgeHighTableOfCache chainEdgeHighTableOfRows
  rw [dif_pos hlengths.2]
  unfold chainTableEdgeInput
  rw [htableValue]
  dsimp [position]
  unfold cachedHashOutputHigh hashOutputHigh at hrow'
  convert hrow' using 1
  cases hcached : cache (Concrete.CacheView.chainInput parameter edge.1 chain
      edge.2 (trajectories[(epochPosition edge.1).val].get
        ⟨edge.2.val, by omega⟩)) <;> simp

def ProgrammedAllEpochTrajectoriesHighRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : List FullChainTrajectory × QueryCache HashSpec)
    (right : (List FullChainTrajectory × QueryCache HashSpec) ×
      List (ChainStep → Digest)) : Prop :=
  left = right.1 ∧
    chainEdgeHighTableOfCache left.2 parameter chain
      (chainValueTableOfList left.1) = chainEdgeHighTableOfRows right.2

theorem relTriple_programmedAllEpochTrajectories_exposes_high
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) :
    RelTriple
      (programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs)
      (programmedFixedSeedChainTrajectoriesWithHigh parameter secret chain
        (chainLength - 1) ∅ allEpochs)
      (ProgrammedAllEpochTrajectoriesHighRelation parameter chain) := by
  apply relTriple_post_mono
    (relTriple_programmedFixedSeedChainTrajectories_exposes_high parameter
      secret chain (chainLength - 1) le_rfl allEpochs ∅ allEpochs_nodup)
  intro left right hrelation
  refine ⟨hrelation.1, ?_⟩
  exact chainEdgeHighTableOfCache_eq_rows parameter chain left.1 left.2 right.2
    hrelation.2.2

noncomputable def programmedWarmedTrajectoryMaterialWithHigh
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (WarmedTrajectoryMaterial × (ChainEdgeIndex → Digest)) := do
  let secretView ← extractFixedChainSeeds chain allEpochs
  let trajectoryHigh ← programmedFixedSeedChainTrajectoriesWithHigh parameter
    (unflattenSecret secretView.2) chain (chainLength - 1) ∅ allEpochs
  pure ((secretView, trajectoryHigh.1),
    chainEdgeHighTableOfRows trajectoryHigh.2)

def ProgrammedWarmedTrajectoryMaterialHighRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : WarmedTrajectoryMaterial)
    (right : WarmedTrajectoryMaterial × (ChainEdgeIndex → Digest)) : Prop :=
  left = right.1 ∧
    chainEdgeHighTableOfCache left.2.2 parameter chain
      (chainValueTableOfList left.2.1) = right.2

theorem relTriple_programmedWarmedTrajectoryMaterial_exposes_high
    (parameter : PublicParameter) (chain : ChainIndex) :
    RelTriple
      (programmedWarmedTrajectoryMaterial parameter chain)
      (programmedWarmedTrajectoryMaterialWithHigh parameter chain)
      (ProgrammedWarmedTrajectoryMaterialHighRelation parameter chain) := by
  unfold programmedWarmedTrajectoryMaterial
    programmedWarmedTrajectoryMaterialWithHigh
  apply relTriple_bind (relTriple_refl (extractFixedChainSeeds chain allEpochs))
  intro leftSecretView rightSecretView hsecretView
  subst rightSecretView
  apply relTriple_bind
    (relTriple_programmedAllEpochTrajectories_exposes_high parameter
      (unflattenSecret leftSecretView.2) chain)
  intro leftTrajectory rightTrajectory htrajectory
  apply relTriple_pure_pure
  exact ⟨congrArg (fun trajectory => (leftSecretView, trajectory)) htrajectory.1,
    htrajectory.2⟩

noncomputable def coupledWarmedKeygenExperimentWithHigh
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (CoupledWarmedKeygenView × (ChainEdgeIndex → Digest)) := do
  let materialHigh ← programmedWarmedTrajectoryMaterialWithHigh parameter chain
  let material := materialHigh.1
  let tree ← treeValues parameter (unflattenSecret material.1.2)
    allTreeValueIndices material.2.2
  pure (({
    secret := unflattenSecret material.1.2
    table := chainValueTableOfList material.2.1
    values := tree.1
    cache := tree.2
  } : CoupledWarmedKeygenView), materialHigh.2)

def CoupledWarmedKeygenHighRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : CoupledWarmedKeygenView)
    (right : CoupledWarmedKeygenView × (ChainEdgeIndex → Digest)) : Prop :=
  left = right.1 ∧
    chainEdgeHighTableOfCache left.cache parameter chain left.table = right.2

set_option maxRecDepth 100000 in
theorem relTriple_coupledWarmedKeygenExperiment_exposes_high
    (parameter : PublicParameter) (chain : ChainIndex) :
    RelTriple
      (coupledWarmedKeygenExperiment parameter chain)
      (coupledWarmedKeygenExperimentWithHigh parameter chain)
      (CoupledWarmedKeygenHighRelation parameter chain) := by
  unfold coupledWarmedKeygenExperiment coupledWarmedKeygenExperimentWithHigh
  apply relTriple_bind (relTriple_with_support
    (relTriple_programmedWarmedTrajectoryMaterial_exposes_high parameter chain))
  intro leftMaterial rightMaterial hmaterial
  rcases hmaterial with ⟨⟨hmaterialEq, hmaterialHigh⟩,
    hleftMaterial, _hrightMaterial⟩
  subst leftMaterial
  apply relTriple_bind (relTriple_with_support (relTriple_refl
    (treeValues parameter (unflattenSecret rightMaterial.1.1.2)
      allTreeValueIndices rightMaterial.1.2.2)))
  intro leftTree rightTree htree
  rcases htree with ⟨htreeEq, hleftTree, _hrightTree⟩
  subst leftTree
  apply relTriple_pure_pure
  refine ⟨rfl, ?_⟩
  have htrajectory := programmedWarmedTrajectoryMaterial_support_trajectory
    parameter chain rightMaterial.1 hleftMaterial
  have hmatches := programmedFixedSeedChainTrajectories_edgesMatch parameter
    (unflattenSecret rightMaterial.1.1.2) chain rightMaterial.1.2 htrajectory
  have hcacheLe := treeValues_cache_le parameter
    (unflattenSecret rightMaterial.1.1.2) allTreeValueIndices
      rightMaterial.1.2.2 rightTree hleftTree
  exact (chainEdgeHighTableOfCache_mono rightMaterial.1.2.2 rightTree.2
    parameter chain (chainValueTableOfList rightMaterial.1.2.1)
      hmatches hcacheLe).symm.trans hmaterialHigh

noncomputable def coupledWarmedFixedChainKeygenWithHigh
    (chain : ChainIndex) :
    ProbComp (ProgrammedFixedChainKeygenView × (ChainEdgeIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let viewHigh ← coupledWarmedKeygenExperimentWithHigh parameter chain
  pure (viewHigh.1.toProgrammedView parameter, viewHigh.2)

def ProgrammedWarmedFixedChainKeygenHighRelation
    (chain : ChainIndex) (left : ProgrammedFixedChainKeygenView)
    (right : ProgrammedFixedChainKeygenView × (ChainEdgeIndex → Digest)) : Prop :=
  left = right.1 ∧
    chainEdgeHighTableOfCache left.cache left.secretKey.parameter chain
      left.table = right.2

theorem relTriple_programmedWarmedFixedChainKeygen_exposes_high
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (coupledWarmedFixedChainKeygenWithHigh chain)
      (ProgrammedWarmedFixedChainKeygenHighRelation chain) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_coupledWarmedFixedChainKeygen_eq_programmed chain).symm
  unfold coupledWarmedFixedChainKeygen
    coupledWarmedFixedChainKeygenWithHigh
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledWarmedKeygenExperiment_exposes_high leftParameter chain)
  intro leftView rightView hview
  apply relTriple_pure_pure
  refine ⟨congrArg (CoupledWarmedKeygenView.toProgrammedView leftParameter)
    hview.1, ?_⟩
  simpa [CoupledWarmedKeygenView.toProgrammedView] using hview.2

theorem evalDist_coupledWarmedFixedChainKeygenWithHigh_fst_eq_actual
    (chain : ChainIndex) :
    evalDist (Prod.fst <$> coupledWarmedFixedChainKeygenWithHigh chain) =
      evalDist (actualFixedChainKeygen chain) := by
  have hcoupling := relTriple_post_mono
    (relTriple_programmedWarmedFixedChainKeygen_exposes_high chain)
    (fun left right hrelation => hrelation.1)
  calc
    evalDist (Prod.fst <$> coupledWarmedFixedChainKeygenWithHigh chain) =
        evalDist (id <$> programmedWarmedFixedChainKeygen chain) :=
      (evalDist_map_eq_of_relTriple hcoupling).symm
    _ = evalDist (programmedWarmedFixedChainKeygen chain) := by simp
    _ = evalDist (actualFixedChainKeygen chain) :=
      (evalDist_actualFixedChainKeygen_eq_programmedWarmed chain).symm

end XmssSecurity
