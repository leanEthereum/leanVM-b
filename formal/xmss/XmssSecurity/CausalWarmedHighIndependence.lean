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

def appendChainHigh {steps : Nat} (prior : Fin steps → Digest)
    (high : Digest) : Fin (steps + 1) → Digest :=
  Fin.lastCases high prior

def finLastCasesEquiv (steps : Nat) :
    ((Fin steps → Digest) × Digest) ≃ (Fin (steps + 1) → Digest) where
  toFun pair := appendChainHigh pair.1 pair.2
  invFun values := (fun index => values index.castSucc, values (Fin.last steps))
  left_inv pair := by
    apply Prod.ext
    · funext index
      simp [appendChainHigh]
    · simp [appendChainHigh]
  right_inv values := by
    funext index
    cases index using Fin.lastCases <;> simp [appendChainHigh]

noncomputable def sampleChainHighRow :
    (steps : Nat) → ProbComp (Fin steps → Digest)
  | 0 => pure (fun index => Fin.elim0 index)
  | steps + 1 => do
      let prior ← sampleChainHighRow steps
      let high ← $ᵗ Digest
      pure (appendChainHigh prior high)

theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] :
    evalDist (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) =
    evalDist ($ᵗ (α × β)) := by
  apply SPMF.ext
  intro target
  rw [show (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) = Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) by
    simp [monad_norm]]
  change Pr[= target | Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)] =
    Pr[= target | $ᵗ (α × β)]
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

set_option maxRecDepth 100000 in
theorem evalDist_sampleChainHighRow_eq_uniform : ∀ steps : Nat,
    evalDist (sampleChainHighRow steps) =
      evalDist ($ᵗ (Fin steps → Digest)) := by
  intro steps
  induction steps with
  | zero =>
      apply SPMF.ext
      intro target
      have htarget : target = fun index => Fin.elim0 index := by
        funext index
        exact Fin.elim0 index
      subst target
      simp [sampleChainHighRow]
  | succ steps ih =>
      rw [sampleChainHighRow]
      calc
        evalDist (sampleChainHighRow steps >>= fun prior =>
            ($ᵗ Digest) >>= fun high =>
              pure (appendChainHigh prior high)) =
            evalDist (($ᵗ (Fin steps → Digest)) >>= fun prior =>
              ($ᵗ Digest) >>= fun high =>
                pure (appendChainHigh prior high)) := by
          rw [evalDist_bind, ih, ← evalDist_bind]
        _ = evalDist ((finLastCasesEquiv steps) <$> (do
              let prior ← $ᵗ (Fin steps → Digest)
              let high ← $ᵗ Digest
              pure (prior, high))) := by
          simp [finLastCasesEquiv, map_eq_bind_pure_comp,
            bind_assoc]
        _ = evalDist ((finLastCasesEquiv steps) <$> ($ᵗ
              ((Fin steps → Digest) × Digest))) := by
          rw [evalDist_map,
            evalDist_independent_uniform_pair
              (α := Fin steps → Digest) (β := Digest), ← evalDist_map]
        _ = evalDist ($ᵗ (Fin (steps + 1) → Digest)) :=
          evalDist_map_bijective_uniform_cross
            (α := (Fin steps → Digest) × Digest)
            (β := Fin (steps + 1) → Digest)
            (finLastCasesEquiv steps) (finLastCasesEquiv steps).bijective

noncomputable def sampleChainHighRows (steps : Nat) :
    (count : Nat) → ProbComp (List (Fin steps → Digest))
  | 0 => pure []
  | count + 1 => do
      let first ← sampleChainHighRow steps
      let rest ← sampleChainHighRows steps count
      pure (first :: rest)

def finConsEquiv (α : Type) (count : Nat) :
    (α × (Fin count → α)) ≃ (Fin (count + 1) → α) where
  toFun pair := Fin.cases pair.1 pair.2
  invFun values := (values 0, fun index => values index.succ)
  left_inv pair := by
    apply Prod.ext
    · simp
    · funext index
      simp
  right_inv values := by
    funext index
    cases index using Fin.cases <;> simp

set_option maxRecDepth 100000 in
theorem evalDist_sampleChainHighRows_eq_uniformRows
    (steps count : Nat) :
    evalDist (sampleChainHighRows steps count) =
      evalDist (List.ofFn <$> ($ᵗ
        (Fin count → (Fin steps → Digest)))) := by
  induction count with
  | zero =>
      rw [sampleChainHighRows]
      symm
      rw [map_eq_bind_pure_comp]
      calc
        evalDist (($ᵗ (Fin 0 → (Fin steps → Digest))) >>= fun values =>
            pure (List.ofFn values)) =
            evalDist (($ᵗ (Fin 0 → (Fin steps → Digest))) >>= fun _values =>
              pure []) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro values
          have hnil : List.ofFn values = [] :=
            List.eq_nil_of_length_eq_zero (by simp)
          rw [hnil]
        _ = evalDist (pure []) :=
          OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            ($ᵗ (Fin 0 → (Fin steps → Digest)))
            (probFailure_eq_zero' inferInstance) (pure [])
  | succ count ih =>
      rw [sampleChainHighRows]
      calc
        evalDist (sampleChainHighRow steps >>= fun first =>
            sampleChainHighRows steps count >>= fun rest =>
              pure (first :: rest)) =
            evalDist (($ᵗ (Fin steps → Digest)) >>= fun first =>
              sampleChainHighRows steps count >>= fun rest =>
                pure (first :: rest)) := by
          rw [evalDist_bind,
            evalDist_sampleChainHighRow_eq_uniform steps, ← evalDist_bind]
        _ = evalDist (($ᵗ (Fin steps → Digest)) >>= fun first =>
              (List.ofFn <$> ($ᵗ
                (Fin count → (Fin steps → Digest)))) >>= fun rest =>
                pure (first :: rest)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          rw [evalDist_bind, ih, ← evalDist_bind]
        _ = evalDist (List.ofFn <$> ((finConsEquiv
              (Fin steps → Digest) count) <$> (do
                let first ← $ᵗ (Fin steps → Digest)
                let rest ← $ᵗ (Fin count → (Fin steps → Digest))
                pure (first, rest)))) := by
          simp [finConsEquiv, map_eq_bind_pure_comp,
            bind_assoc]
        _ = evalDist (List.ofFn <$> ((finConsEquiv
              (Fin steps → Digest) count) <$> ($ᵗ
                ((Fin steps → Digest) ×
                  (Fin count → (Fin steps → Digest)))))) := by
          rw [evalDist_map, evalDist_map,
            evalDist_independent_uniform_pair
              (α := Fin steps → Digest)
              (β := Fin count → (Fin steps → Digest)),
            ← evalDist_map, ← evalDist_map]
        _ = evalDist (List.ofFn <$> ($ᵗ
              (Fin (count + 1) → (Fin steps → Digest)))) := by
          rw [evalDist_map,
            evalDist_map_bijective_uniform_cross
              (α := (Fin steps → Digest) ×
                (Fin count → (Fin steps → Digest)))
              (β := Fin (count + 1) → (Fin steps → Digest))
              (finConsEquiv (Fin steps → Digest) count)
                (finConsEquiv (Fin steps → Digest) count).bijective,
            ← evalDist_map]

noncomputable def programmedChainValues :
    (position : Nat) → (steps : Nat) → Digest → ProbComp (Vector Digest (steps + 1))
  | _position, 0, value => pure (Vector.ofFn fun _ => value)
  | position, steps + 1, value => do
      let prior ← programmedChainValues position steps value
      if position + steps < chainLength - 1 then
        let low ← $ᵗ Digest
        pure (prior.push low)
      else
        pure (prior.push 0)

theorem evalDist_programmedChainExtension_values
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    evalDist (Prod.fst <$>
      programmedChainExtension parameter epoch chain step values cache) =
    evalDist (do
      let low ← $ᵗ Digest
      pure (values.push low)) := by
  unfold programmedChainExtension Rom.sampledHashOutputWithDigest
    Rom.sampleHashOutputWithDigest
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro low
  exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    ($ᵗ Digest) (probFailure_eq_zero' inferInstance)
      (pure (values.push low))

theorem evalDist_programmedChainExtensionWithHigh_values
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    evalDist ((fun result => (result.1.1, result.2)) <$>
      programmedChainExtensionWithHigh parameter epoch chain step values cache) =
    evalDist (do
      let low ← $ᵗ Digest
      let high ← $ᵗ Digest
      pure (values.push low, high)) := by
  unfold programmedChainExtensionWithHigh
  simp [map_eq_bind_pure_comp, bind_assoc]

set_option maxRecDepth 100000 in
theorem evalDist_programmedChainTrajectory_values
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec),
    evalDist (Prod.fst <$>
      programmedChainTrajectory parameter epoch chain position steps value cache) =
    evalDist (programmedChainValues position steps value) := by
  intro steps
  induction steps with
  | zero =>
      intro value cache
      simp [programmedChainTrajectory, programmedChainValues]
  | succ steps ih =>
      intro value cache
      rw [programmedChainTrajectory, programmedChainValues]
      split <;> rename_i hvalid
      · simp only [map_eq_bind_pure_comp, bind_assoc]
        calc
          evalDist (programmedChainTrajectory parameter epoch chain position
              steps value cache >>= fun prior =>
                programmedChainExtension parameter epoch chain
                  ⟨position + steps, hvalid⟩ prior.1 prior.2 >>= fun extended =>
                    pure extended.1) =
              evalDist (programmedChainTrajectory parameter epoch chain position
                steps value cache >>= fun prior =>
                  ($ᵗ Digest) >>= fun low => pure (prior.1.push low)) := by
            apply OracleComp.DeferredSampling.evalDist_bind_congr_left
            intro prior
            simpa [map_eq_bind_pure_comp, bind_assoc] using
              (evalDist_programmedChainExtension_values parameter epoch chain
                ⟨position + steps, hvalid⟩ prior.1 prior.2)
          _ = evalDist ((Prod.fst <$> programmedChainTrajectory parameter epoch
                chain position steps value cache) >>= fun prior =>
                  ($ᵗ Digest) >>= fun low => pure (prior.push low)) := by
            simp [map_eq_bind_pure_comp, bind_assoc]
          _ = evalDist (programmedChainValues position steps value >>= fun prior =>
                ($ᵗ Digest) >>= fun low => pure (prior.push low)) := by
            rw [evalDist_bind, ih value cache, ← evalDist_bind]
      · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        calc
          evalDist (programmedChainTrajectory parameter epoch chain position
              steps value cache >>= fun prior => pure (prior.1.push 0)) =
              evalDist ((Prod.fst <$> programmedChainTrajectory parameter epoch
                chain position steps value cache) >>= fun prior =>
                  pure (prior.push 0)) := by
            simp [map_eq_bind_pure_comp, bind_assoc]
          _ = evalDist (programmedChainValues position steps value >>= fun prior =>
                pure (prior.push 0)) := by
            rw [evalDist_bind, ih value cache, ← evalDist_bind]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_programmedChainTrajectoryWithHigh_values_high
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec)
      (_hbound : position + steps ≤ chainLength - 1),
    evalDist ((fun result => (result.1.1, result.2)) <$>
      programmedChainTrajectoryWithHigh parameter epoch chain position steps
        value cache) =
    evalDist (do
      let values ← programmedChainValues position steps value
      let high ← sampleChainHighRow steps
      pure (values, high)) := by
  intro steps
  induction steps with
  | zero =>
      intro value cache hbound
      simp [programmedChainTrajectoryWithHigh, programmedChainValues,
        sampleChainHighRow]
  | succ steps ih =>
      intro value cache hbound
      have hvalid : position + steps < chainLength - 1 := by omega
      rw [programmedChainTrajectoryWithHigh]
      simp only [hvalid, ↓reduceDIte, map_eq_bind_pure_comp, bind_assoc,
        pure_bind, Function.comp_apply]
      calc
        evalDist (programmedChainTrajectoryWithHigh parameter epoch chain
            position steps value cache >>= fun prior =>
          programmedChainExtensionWithHigh parameter epoch chain
              ⟨position + steps, hvalid⟩ prior.1.1 prior.1.2 >>= fun extended =>
            pure (extended.1.1, appendChainHigh prior.2 extended.2)) =
          evalDist (programmedChainTrajectoryWithHigh parameter epoch chain
              position steps value cache >>= fun prior =>
            ($ᵗ Digest) >>= fun low =>
            ($ᵗ Digest) >>= fun high =>
              pure (prior.1.1.push low,
                appendChainHigh prior.2 high)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro prior
          calc
            evalDist (programmedChainExtensionWithHigh parameter epoch chain
                ⟨position + steps, hvalid⟩ prior.1.1 prior.1.2 >>= fun extended =>
                  pure (extended.1.1,
                    appendChainHigh prior.2 extended.2)) =
              evalDist (((fun result => (result.1.1, result.2)) <$>
                programmedChainExtensionWithHigh parameter epoch chain
                  ⟨position + steps, hvalid⟩ prior.1.1 prior.1.2) >>= fun result =>
                    pure (result.1, appendChainHigh prior.2 result.2)) := by
                simp [map_eq_bind_pure_comp, bind_assoc]
            _ = evalDist ((do
                  let low ← $ᵗ Digest
                  let high ← $ᵗ Digest
                  pure (prior.1.1.push low, high)) >>= fun result =>
                    pure (result.1, appendChainHigh prior.2 result.2)) := by
                rw [evalDist_bind,
                  evalDist_programmedChainExtensionWithHigh_values parameter
                    epoch chain ⟨position + steps, hvalid⟩ prior.1.1 prior.1.2,
                  ← evalDist_bind]
            _ = evalDist (($ᵗ Digest) >>= fun low =>
                  ($ᵗ Digest) >>= fun high =>
                    pure (prior.1.1.push low,
                      appendChainHigh prior.2 high)) := by
                simp
        _ = evalDist (((fun result => (result.1.1, result.2)) <$>
              programmedChainTrajectoryWithHigh parameter epoch chain position
                steps value cache) >>= fun prior =>
            ($ᵗ Digest) >>= fun low =>
            ($ᵗ Digest) >>= fun high =>
              pure (prior.1.push low,
                appendChainHigh prior.2 high)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist ((programmedChainValues position steps value >>= fun values =>
              sampleChainHighRow steps >>= fun priorHigh =>
                pure (values, priorHigh)) >>= fun prior =>
            ($ᵗ Digest) >>= fun low =>
            ($ᵗ Digest) >>= fun high =>
              pure (prior.1.push low, appendChainHigh prior.2 high)) := by
          rw [evalDist_bind, ih value cache (by omega), ← evalDist_bind]
        _ = evalDist (programmedChainValues position steps value >>= fun values =>
              sampleChainHighRow steps >>= fun priorHigh =>
              ($ᵗ Digest) >>= fun low =>
              ($ᵗ Digest) >>= fun high =>
                pure (values.push low, appendChainHigh priorHigh high)) := by
          simp [bind_assoc]
        _ = evalDist (programmedChainValues position steps value >>= fun values =>
              ($ᵗ Digest) >>= fun low =>
              sampleChainHighRow steps >>= fun priorHigh =>
              ($ᵗ Digest) >>= fun high =>
                pure (values.push low, appendChainHigh priorHigh high)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro values
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            (sampleChainHighRow steps) ($ᵗ Digest)
              (fun priorHigh low => ($ᵗ Digest) >>= fun high =>
                pure (values.push low, appendChainHigh priorHigh high))
        _ = evalDist ((programmedChainValues position steps value >>= fun values =>
              ($ᵗ Digest) >>= fun low => pure (values.push low)) >>= fun values =>
            (sampleChainHighRow steps >>= fun priorHigh =>
              ($ᵗ Digest) >>= fun high =>
                pure (appendChainHigh priorHigh high)) >>= fun high =>
              pure (values, high)) := by
          simp [bind_assoc]
        _ = evalDist (do
              let values ← programmedChainValues position (steps + 1) value
              let high ← sampleChainHighRow (steps + 1)
              pure (values, high)) := by
          rw [programmedChainValues, sampleChainHighRow]
          simp [hvalid, bind_assoc]
      rfl

noncomputable def programmedFixedSeedChainValues
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) : List Epoch →
      ProbComp (List (Vector Digest (steps + 1)))
  | [] => pure []
  | epoch :: epochs => do
      let first ← programmedChainValues 0 steps (secret epoch chain)
      let rest ← programmedFixedSeedChainValues secret chain steps epochs
      pure (first :: rest)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem evalDist_programmedFixedSeedChainTrajectories_values
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) : ∀
      (epochs : List Epoch) (cache : QueryCache HashSpec),
    evalDist (Prod.fst <$> programmedFixedSeedChainTrajectoriesFromCache
      parameter secret chain steps cache epochs) =
    evalDist (programmedFixedSeedChainValues secret chain steps epochs) := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache
      simp [programmedFixedSeedChainTrajectoriesFromCache,
        programmedFixedSeedChainValues]
  | cons epoch epochs ih =>
      intro cache
      rw [programmedFixedSeedChainTrajectoriesFromCache_cons,
        programmedFixedSeedChainValues]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      calc
        evalDist (programmedChainTrajectory parameter epoch chain 0 steps
            (secret epoch chain) cache >>= fun first =>
          programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
              steps first.2 epochs >>= fun rest =>
            pure (first.1 :: rest.1)) =
          evalDist (programmedChainTrajectory parameter epoch chain 0 steps
              (secret epoch chain) cache >>= fun first =>
            programmedFixedSeedChainValues secret chain steps epochs >>= fun rest =>
              pure (first.1 :: rest)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          calc
            evalDist (programmedFixedSeedChainTrajectoriesFromCache parameter
                secret chain steps first.2 epochs >>= fun rest =>
                  pure (first.1 :: rest.1)) =
              evalDist ((Prod.fst <$>
                programmedFixedSeedChainTrajectoriesFromCache parameter secret
                  chain steps first.2 epochs) >>= fun rest =>
                    pure (first.1 :: rest)) := by
                simp [map_eq_bind_pure_comp, bind_assoc]
            _ = evalDist (programmedFixedSeedChainValues secret chain steps
                  epochs >>= fun rest => pure (first.1 :: rest)) := by
                rw [evalDist_bind, ih first.2, ← evalDist_bind]
        _ = evalDist ((Prod.fst <$> programmedChainTrajectory parameter epoch
              chain 0 steps (secret epoch chain) cache) >>= fun first =>
            programmedFixedSeedChainValues secret chain steps epochs >>= fun rest =>
              pure (first :: rest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (programmedChainValues 0 steps (secret epoch chain) >>=
            fun first =>
              programmedFixedSeedChainValues secret chain steps epochs >>= fun rest =>
                pure (first :: rest)) := by
          rw [evalDist_bind,
            evalDist_programmedChainTrajectory_values parameter epoch chain 0
              steps (secret epoch chain) cache,
            ← evalDist_bind]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_programmedFixedSeedChainTrajectoriesWithHigh_values_high
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) : ∀
      (epochs : List Epoch) (cache : QueryCache HashSpec),
    evalDist ((fun result => (result.1.1, result.2)) <$>
      programmedFixedSeedChainTrajectoriesWithHigh parameter secret chain steps
        cache epochs) =
    evalDist (do
      let trajectories ← programmedFixedSeedChainValues secret chain steps epochs
      let highs ← sampleChainHighRows steps epochs.length
      pure (trajectories, highs)) := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache
      simp [programmedFixedSeedChainTrajectoriesWithHigh,
        programmedFixedSeedChainValues, sampleChainHighRows]
  | cons epoch epochs ih =>
      intro cache
      rw [programmedFixedSeedChainTrajectoriesWithHigh]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      calc
        evalDist (programmedChainTrajectoryWithHigh parameter epoch chain 0
            steps (secret epoch chain) cache >>= fun first =>
          programmedFixedSeedChainTrajectoriesWithHigh parameter secret chain
              steps first.1.2 epochs >>= fun rest =>
            pure (first.1.1 :: rest.1.1, first.2 :: rest.2)) =
          evalDist (programmedChainTrajectoryWithHigh parameter epoch chain 0
              steps (secret epoch chain) cache >>= fun first =>
            (programmedFixedSeedChainValues secret chain steps epochs >>= fun rest =>
              sampleChainHighRows steps epochs.length >>= fun restHigh =>
                pure (rest, restHigh)) >>= fun rest =>
              pure (first.1.1 :: rest.1, first.2 :: rest.2)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          calc
            evalDist (programmedFixedSeedChainTrajectoriesWithHigh parameter
                secret chain steps first.1.2 epochs >>= fun rest =>
                  pure (first.1.1 :: rest.1.1, first.2 :: rest.2)) =
              evalDist (((fun result => (result.1.1, result.2)) <$>
                programmedFixedSeedChainTrajectoriesWithHigh parameter secret
                  chain steps first.1.2 epochs) >>= fun rest =>
                    pure (first.1.1 :: rest.1, first.2 :: rest.2)) := by
                simp [map_eq_bind_pure_comp, bind_assoc]
            _ = evalDist ((programmedFixedSeedChainValues secret chain steps
                  epochs >>= fun rest =>
                sampleChainHighRows steps epochs.length >>= fun restHigh =>
                  pure (rest, restHigh)) >>= fun rest =>
                    pure (first.1.1 :: rest.1, first.2 :: rest.2)) := by
                rw [evalDist_bind, ih first.1.2, ← evalDist_bind]
        _ = evalDist (((fun result => (result.1.1, result.2)) <$>
              programmedChainTrajectoryWithHigh parameter epoch chain 0 steps
                (secret epoch chain) cache) >>= fun first =>
            (programmedFixedSeedChainValues secret chain steps epochs >>= fun rest =>
              sampleChainHighRows steps epochs.length >>= fun restHigh =>
                pure (rest, restHigh)) >>= fun rest =>
              pure (first.1 :: rest.1, first.2 :: rest.2)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist ((programmedChainValues 0 steps (secret epoch chain) >>=
              fun first =>
                sampleChainHighRow steps >>= fun firstHigh =>
                  pure (first, firstHigh)) >>= fun first =>
            (programmedFixedSeedChainValues secret chain steps epochs >>= fun rest =>
              sampleChainHighRows steps epochs.length >>= fun restHigh =>
                pure (rest, restHigh)) >>= fun rest =>
              pure (first.1 :: rest.1, first.2 :: rest.2)) := by
          rw [evalDist_bind,
            evalDist_programmedChainTrajectoryWithHigh_values_high parameter
              epoch chain 0 steps (secret epoch chain) cache (by omega),
            ← evalDist_bind]
        _ = evalDist (programmedChainValues 0 steps (secret epoch chain) >>=
            fun first =>
              sampleChainHighRow steps >>= fun firstHigh =>
              programmedFixedSeedChainValues secret chain steps epochs >>= fun rest =>
              sampleChainHighRows steps epochs.length >>= fun restHigh =>
                pure (first :: rest, firstHigh :: restHigh)) := by
          simp [bind_assoc]
        _ = evalDist (programmedChainValues 0 steps (secret epoch chain) >>=
            fun first =>
              programmedFixedSeedChainValues secret chain steps epochs >>= fun rest =>
              sampleChainHighRow steps >>= fun firstHigh =>
              sampleChainHighRows steps epochs.length >>= fun restHigh =>
                pure (first :: rest, firstHigh :: restHigh)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            (sampleChainHighRow steps)
            (programmedFixedSeedChainValues secret chain steps epochs)
            (fun firstHigh rest =>
              sampleChainHighRows steps epochs.length >>= fun restHigh =>
                pure (first :: rest, firstHigh :: restHigh))
        _ = evalDist (do
              let trajectories ← programmedFixedSeedChainValues secret chain
                steps (epoch :: epochs)
              let highs ← sampleChainHighRows steps (epoch :: epochs).length
              pure (trajectories, highs)) := by
          rw [programmedFixedSeedChainValues, List.length_cons,
            sampleChainHighRows]
          simp [bind_assoc]
      rfl

theorem epochPosition_allEpochs_get
    (position : Fin allEpochs.length) :
    epochPosition (allEpochs.get position) = position := by
  apply Fin.ext
  unfold epochPosition
  simpa using allEpochs_nodup.idxOf_getElem position

noncomputable def chainEdgeHighRowsEquiv :
    (Fin allEpochs.length → (ChainStep → Digest)) ≃
      (ChainEdgeIndex → Digest) where
  toFun rows edge := rows (epochPosition edge.1) edge.2
  invFun table position step := table (allEpochs.get position, step)
  left_inv rows := by
    funext position step
    change rows (epochPosition (allEpochs.get position)) step = rows position step
    rw [epochPosition_allEpochs_get]
  right_inv table := by
    funext edge
    change table (allEpochs.get (epochPosition edge.1), edge.2) = table edge
    rw [allEpochs_get_epochPosition]

theorem chainEdgeHighTableOfRows_ofFn
    (rows : Fin allEpochs.length → (ChainStep → Digest)) :
    chainEdgeHighTableOfRows (List.ofFn rows) =
      chainEdgeHighRowsEquiv rows := by
  funext edge
  unfold chainEdgeHighTableOfRows chainEdgeHighRowsEquiv
  rw [dif_pos (by simp)]
  simp

set_option maxRecDepth 100000 in
theorem evalDist_chainEdgeHighTableOfRows_sample_eq_uniform :
    evalDist (chainEdgeHighTableOfRows <$>
      sampleChainHighRows (chainLength - 1) allEpochs.length) =
    evalDist ($ᵗ (ChainEdgeIndex → Digest)) := by
  calc
    evalDist (chainEdgeHighTableOfRows <$>
        sampleChainHighRows (chainLength - 1) allEpochs.length) =
      evalDist (chainEdgeHighTableOfRows <$> (List.ofFn <$> ($ᵗ
        (Fin allEpochs.length → (ChainStep → Digest))))) := by
        rw [evalDist_map,
          evalDist_sampleChainHighRows_eq_uniformRows
            (chainLength - 1) allEpochs.length,
          ← evalDist_map]
    _ = evalDist (chainEdgeHighRowsEquiv <$> ($ᵗ
          (Fin allEpochs.length → (ChainStep → Digest)))) := by
      simp only [Functor.map_map]
      congr 2
      funext rows
      exact chainEdgeHighTableOfRows_ofFn rows
    _ = evalDist ($ᵗ (ChainEdgeIndex → Digest)) :=
      evalDist_map_bijective_uniform_cross
        (α := Fin allEpochs.length → (ChainStep → Digest))
        (β := ChainEdgeIndex → Digest)
        chainEdgeHighRowsEquiv chainEdgeHighRowsEquiv.bijective

noncomputable def programmedWarmedOutsideTableHighView
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((OutsideChainSecret chain × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) :=
  (fun materialHigh =>
    ((outsideChainSecret chain materialHigh.1.1.2,
      chainValueTableOfList materialHigh.1.2.1), materialHigh.2)) <$>
        programmedWarmedTrajectoryMaterialWithHigh parameter chain

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedOutsideTableHighView_eq_appendUniform
    (parameter : PublicParameter) (chain : ChainIndex) :
    evalDist (programmedWarmedOutsideTableHighView parameter chain) =
    evalDist (do
      let outsideTable ← programmedWarmedOutsideTableView parameter chain
      let high ← $ᵗ (ChainEdgeIndex → Digest)
      pure (outsideTable, high)) := by
  unfold programmedWarmedOutsideTableHighView
    programmedWarmedTrajectoryMaterialWithHigh
    programmedWarmedOutsideTableView programmedWarmedTrajectoryMaterial
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secretView
  let finish := fun result :
      List FullChainTrajectory × List (ChainStep → Digest) =>
    ((outsideChainSecret chain secretView.2,
      chainValueTableOfList result.1), chainEdgeHighTableOfRows result.2)
  calc
    evalDist (programmedFixedSeedChainTrajectoriesWithHigh parameter
        (unflattenSecret secretView.2) chain (chainLength - 1) ∅ allEpochs >>=
      fun trajectoryHigh => pure
        ((outsideChainSecret chain secretView.2,
          chainValueTableOfList trajectoryHigh.1.1),
            chainEdgeHighTableOfRows trajectoryHigh.2)) =
      evalDist (finish <$> ((fun result => (result.1.1, result.2)) <$>
        programmedFixedSeedChainTrajectoriesWithHigh parameter
          (unflattenSecret secretView.2) chain (chainLength - 1) ∅
            allEpochs)) := by
        simp [finish, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (finish <$> (do
          let trajectories ← programmedFixedSeedChainValues
            (unflattenSecret secretView.2) chain (chainLength - 1) allEpochs
          let highs ← sampleChainHighRows (chainLength - 1) allEpochs.length
          pure (trajectories, highs))) := by
      rw [evalDist_map,
        evalDist_programmedFixedSeedChainTrajectoriesWithHigh_values_high
          parameter (unflattenSecret secretView.2) chain (chainLength - 1)
            le_rfl allEpochs ∅,
        ← evalDist_map]
    _ = evalDist (programmedFixedSeedChainValues
          (unflattenSecret secretView.2) chain (chainLength - 1) allEpochs >>=
        fun trajectories =>
          (chainEdgeHighTableOfRows <$>
            sampleChainHighRows (chainLength - 1) allEpochs.length) >>= fun high =>
              pure ((outsideChainSecret chain secretView.2,
                chainValueTableOfList trajectories), high)) := by
      simp [finish, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (programmedFixedSeedChainValues
          (unflattenSecret secretView.2) chain (chainLength - 1) allEpochs >>=
        fun trajectories =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
            pure ((outsideChainSecret chain secretView.2,
              chainValueTableOfList trajectories), high)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro trajectories
      rw [evalDist_bind,
        evalDist_chainEdgeHighTableOfRows_sample_eq_uniform,
        ← evalDist_bind]
    _ = evalDist ((Prod.fst <$>
          programmedFixedSeedChainTrajectoriesFromCache parameter
            (unflattenSecret secretView.2) chain (chainLength - 1) ∅
              allEpochs) >>= fun trajectories =>
        ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
          pure ((outsideChainSecret chain secretView.2,
            chainValueTableOfList trajectories), high)) := by
      rw [evalDist_bind,
        ← evalDist_programmedFixedSeedChainTrajectories_values parameter
          (unflattenSecret secretView.2) chain (chainLength - 1) allEpochs ∅,
        ← evalDist_bind]
    _ = evalDist (programmedFixedSeedChainTrajectoriesFromCache parameter
          (unflattenSecret secretView.2) chain (chainLength - 1) ∅ allEpochs >>=
        fun trajectories =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
            pure ((outsideChainSecret chain secretView.2,
              chainValueTableOfList trajectories.1), high)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_programmedWarmedOutsideTableHighView_eq_independent
    (parameter : PublicParameter) (chain : ChainIndex) :
    evalDist (programmedWarmedOutsideTableHighView parameter chain) =
    evalDist (do
      let outsideTable ← independentOutsideTableView chain
      let high ← $ᵗ (ChainEdgeIndex → Digest)
      pure (outsideTable, high)) := by
  calc
    evalDist (programmedWarmedOutsideTableHighView parameter chain) =
        evalDist (programmedWarmedOutsideTableView parameter chain >>= fun view =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
            pure (view, high)) :=
      evalDist_programmedWarmedOutsideTableHighView_eq_appendUniform
        parameter chain
    _ = evalDist (independentOutsideTableView chain >>= fun view =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
            pure (view, high)) := by
      rw [evalDist_bind,
        evalDist_programmedWarmedOutsideTableView_eq_independent parameter chain,
        ← evalDist_bind]

noncomputable def programmedWarmedOutsideHighView
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp (OutsideChainSecret chain × (ChainEdgeIndex → Digest)) :=
  (fun result => (result.1.1, result.2)) <$>
    programmedWarmedOutsideTableHighView parameter chain

theorem evalDist_programmedWarmedOutsideHighView_eq_independent
    (parameter : PublicParameter) (chain : ChainIndex) :
    evalDist (programmedWarmedOutsideHighView parameter chain) =
    evalDist (do
      let outside ← $ᵗ (OutsideChainSecret chain)
      let high ← $ᵗ (ChainEdgeIndex → Digest)
      pure (outside, high)) := by
  unfold programmedWarmedOutsideHighView
  calc
    evalDist ((fun result => (result.1.1, result.2)) <$>
        programmedWarmedOutsideTableHighView parameter chain) =
      evalDist ((fun result => (result.1.1, result.2)) <$> (do
        let outsideTable ← independentOutsideTableView chain
        let high ← $ᵗ (ChainEdgeIndex → Digest)
        pure (outsideTable, high))) := by
          rw [evalDist_map,
            evalDist_programmedWarmedOutsideTableHighView_eq_independent
              parameter chain,
            ← evalDist_map]
    _ = evalDist (($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
          uniformChainValueTable chain >>= fun _table =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
            pure (outside, high)) := by
      unfold independentOutsideTableView
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
            pure (outside, high)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro outside
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (uniformChainValueTable chain) (probFailure_eq_zero' inferInstance)
          (($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
            pure (outside, high))

noncomputable def programmedWarmedTrajectoryMaterialWithBaseHigh
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((WarmedTrajectoryMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) := do
  let materialHigh ← programmedWarmedTrajectoryMaterialWithHigh parameter chain
  let base ← uniformChainValueTable chain
  pure ((materialHigh.1, base), materialHigh.2)

def programmedWarmedMaterialBaseHighView (chain : ChainIndex)
    (result : (WarmedTrajectoryMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) :
    (OutsideChainSecret chain × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest) :=
  ((outsideChainSecret chain result.1.1.1.2, result.1.2), result.2)

set_option maxRecDepth 100000 in
theorem evalDist_programmedWarmedMaterialBaseHighView_eq_independent
    (parameter : PublicParameter) (chain : ChainIndex) :
    evalDist (programmedWarmedMaterialBaseHighView chain <$>
      programmedWarmedTrajectoryMaterialWithBaseHigh parameter chain) =
    evalDist (do
      let outsideTable ← independentOutsideTableView chain
      let high ← $ᵗ (ChainEdgeIndex → Digest)
      pure (outsideTable, high)) := by
  unfold programmedWarmedTrajectoryMaterialWithBaseHigh
    programmedWarmedMaterialBaseHighView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    evalDist (programmedWarmedTrajectoryMaterialWithHigh parameter chain >>=
        fun materialHigh =>
          uniformChainValueTable chain >>= fun base =>
            pure ((outsideChainSecret chain materialHigh.1.1.2, base),
              materialHigh.2)) =
      evalDist (programmedWarmedOutsideHighView parameter chain >>= fun outsideHigh =>
        uniformChainValueTable chain >>= fun base =>
          pure ((outsideHigh.1, base), outsideHigh.2)) := by
        unfold programmedWarmedOutsideHighView
          programmedWarmedOutsideTableHighView
        simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist ((do
          let outside ← $ᵗ (OutsideChainSecret chain)
          let high ← $ᵗ (ChainEdgeIndex → Digest)
          pure (outside, high)) >>= fun outsideHigh =>
        uniformChainValueTable chain >>= fun base =>
          pure ((outsideHigh.1, base), outsideHigh.2)) := by
      rw [evalDist_bind,
        evalDist_programmedWarmedOutsideHighView_eq_independent parameter chain,
        ← evalDist_bind]
    _ = evalDist (($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
          uniformChainValueTable chain >>= fun base =>
            pure ((outside, base), high)) := by
      simp [bind_assoc]
    _ = evalDist (($ᵗ (OutsideChainSecret chain)) >>= fun outside =>
          uniformChainValueTable chain >>= fun base =>
          ($ᵗ (ChainEdgeIndex → Digest)) >>= fun high =>
            pure ((outside, base), high)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro outside
      exact OracleComp.DeferredSampling.evalDist_bind_comm
        ($ᵗ (ChainEdgeIndex → Digest)) (uniformChainValueTable chain)
          (fun high base => pure ((outside, base), high))
    _ = evalDist (do
          let outsideTable ← independentOutsideTableView chain
          let high ← $ᵗ (ChainEdgeIndex → Digest)
          pure (outsideTable, high)) := by
      simp [independentOutsideTableView, bind_assoc]
  rfl

noncomputable def programmedWarmedMaterialTableCacheHighView
    (parameter : PublicParameter) (chain : ChainIndex)
    (material : WarmedTrajectoryMaterial) :
    (OutsideChainSecret chain × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest) :=
  let table := chainValueTableOfList material.2.1
  ((outsideChainSecret chain material.1.2, table),
    chainEdgeHighTableOfCache material.2.2 parameter chain table)

theorem evalDist_programmedWarmedMaterialTableCacheHighView_eq_exposed
    (parameter : PublicParameter) (chain : ChainIndex) :
    evalDist (programmedWarmedMaterialTableCacheHighView parameter chain <$>
      programmedWarmedTrajectoryMaterial parameter chain) =
    evalDist (programmedWarmedOutsideTableHighView parameter chain) := by
  let exposedView := fun result :
      WarmedTrajectoryMaterial × (ChainEdgeIndex → Digest) =>
    ((outsideChainSecret chain result.1.1.2,
      chainValueTableOfList result.1.2.1), result.2)
  have hcoupling := relTriple_post_mono
    (relTriple_programmedWarmedTrajectoryMaterial_exposes_high parameter chain)
    (fun left right hrelation => show
      programmedWarmedMaterialTableCacheHighView parameter chain left =
        exposedView right by
      have hhigh := hrelation.2
      rw [hrelation.1] at hhigh
      unfold programmedWarmedMaterialTableCacheHighView exposedView
      rw [hrelation.1]
      exact congrArg
        (fun high =>
          ((outsideChainSecret chain right.1.1.2,
            chainValueTableOfList right.1.2.1), high)) hhigh)
  calc
    evalDist (programmedWarmedMaterialTableCacheHighView parameter chain <$>
        programmedWarmedTrajectoryMaterial parameter chain) =
      evalDist (exposedView <$>
        programmedWarmedTrajectoryMaterialWithHigh parameter chain) :=
      evalDist_map_eq_of_relTriple hcoupling
    _ = evalDist (programmedWarmedOutsideTableHighView parameter chain) := by
      rfl

theorem evalDist_programmedWarmedTrajectoryMaterialWithHigh_fst_eq
    (parameter : PublicParameter) (chain : ChainIndex) :
    evalDist (Prod.fst <$>
      programmedWarmedTrajectoryMaterialWithHigh parameter chain) =
    evalDist (programmedWarmedTrajectoryMaterial parameter chain) := by
  have hcoupling := relTriple_post_mono
    (relTriple_programmedWarmedTrajectoryMaterial_exposes_high parameter chain)
    (fun left right hrelation => hrelation.1)
  calc
    evalDist (Prod.fst <$>
        programmedWarmedTrajectoryMaterialWithHigh parameter chain) =
      evalDist (id <$>
        programmedWarmedTrajectoryMaterial parameter chain) :=
      (evalDist_map_eq_of_relTriple hcoupling).symm
    _ = evalDist (programmedWarmedTrajectoryMaterial parameter chain) := by
      simp

theorem programmedWarmedTrajectoryMaterialWithBaseHigh_support_material
    (parameter : PublicParameter) (chain : ChainIndex)
    (result : (WarmedTrajectoryMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest))
    (hresult : result ∈ support
      (programmedWarmedTrajectoryMaterialWithBaseHigh parameter chain)) :
    result.1.1 ∈ support
      (programmedWarmedTrajectoryMaterial parameter chain) := by
  unfold programmedWarmedTrajectoryMaterialWithBaseHigh at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨materialHigh, hmaterialHigh, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨base, _hbase, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  apply (mem_support_iff_of_evalDist_eq
    (evalDist_programmedWarmedTrajectoryMaterialWithHigh_fst_eq
      parameter chain) materialHigh.1).mp
  rw [support_map]
  exact ⟨materialHigh, hmaterialHigh, rfl⟩

structure ProgrammedWarmedMaterialBaseHighRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : WarmedTrajectoryMaterial)
    (right : (WarmedTrajectoryMaterial × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) : Prop where
  tableEq : chainValueTableOfList left.2.1 = right.1.2
  highEq : chainEdgeHighTableOfCache left.2.2 parameter chain
      (chainValueTableOfList left.2.1) = right.2
  outsideEq : outsideChainSecret chain left.1.2 =
    outsideChainSecret chain right.1.1.1.2
  leftSupport : left ∈ support
    (programmedWarmedTrajectoryMaterial parameter chain)
  rightSupport : right.1.1 ∈ support
    (programmedWarmedTrajectoryMaterial parameter chain)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_programmedWarmedTrajectoryMaterial_withBaseHigh
    (parameter : PublicParameter) (chain : ChainIndex) :
    RelTriple
      (programmedWarmedTrajectoryMaterial parameter chain)
      (programmedWarmedTrajectoryMaterialWithBaseHigh parameter chain)
      (ProgrammedWarmedMaterialBaseHighRelation parameter chain) := by
  classical
  letI : DecidableEq
      ((OutsideChainSecret chain × (ChainValueIndex → Digest)) ×
        (ChainEdgeIndex → Digest)) := Classical.decEq _
  have hprojection :
      evalDist (programmedWarmedMaterialTableCacheHighView parameter chain <$>
        programmedWarmedTrajectoryMaterial parameter chain) =
      evalDist (programmedWarmedMaterialBaseHighView chain <$>
        programmedWarmedTrajectoryMaterialWithBaseHigh parameter chain) := by
    calc
      _ = evalDist (programmedWarmedOutsideTableHighView parameter chain) :=
        evalDist_programmedWarmedMaterialTableCacheHighView_eq_exposed
          parameter chain
      _ = evalDist (do
          let outsideTable ← independentOutsideTableView chain
          let high ← $ᵗ (ChainEdgeIndex → Digest)
          pure (outsideTable, high)) :=
        evalDist_programmedWarmedOutsideTableHighView_eq_independent
          parameter chain
      _ = _ :=
        (evalDist_programmedWarmedMaterialBaseHighView_eq_independent
          parameter chain).symm
  apply relTriple_post_mono
    (relTriple_of_evalDist_map_eq_with_support_general
      (programmedWarmedTrajectoryMaterial parameter chain)
      (programmedWarmedTrajectoryMaterialWithBaseHigh parameter chain)
      (programmedWarmedMaterialTableCacheHighView parameter chain)
      (programmedWarmedMaterialBaseHighView chain) hprojection)
  intro left right hrelation
  have htable : chainValueTableOfList left.2.1 = right.1.2 :=
    congrArg (fun view => view.1.2) hrelation.1
  have hhigh : chainEdgeHighTableOfCache left.2.2 parameter chain
      (chainValueTableOfList left.2.1) = right.2 :=
    congrArg Prod.snd hrelation.1
  have houtside : outsideChainSecret chain left.1.2 =
      outsideChainSecret chain right.1.1.1.2 :=
    congrArg (fun view => view.1.1) hrelation.1
  exact ⟨htable, hhigh, houtside, hrelation.2.1,
    programmedWarmedTrajectoryMaterialWithBaseHigh_support_material
      parameter chain right hrelation.2.2⟩

noncomputable def coupledWarmedKeygenWithBaseHigh
    (parameter : PublicParameter) (chain : ChainIndex) :
    ProbComp ((CoupledWarmedKeygenView × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) := do
  let materialBaseHigh ←
    programmedWarmedTrajectoryMaterialWithBaseHigh parameter chain
  let material := materialBaseHigh.1.1
  let tree ← treeValues parameter (unflattenSecret material.1.2)
    allTreeValueIndices material.2.2
  pure ((({
    secret := unflattenSecret material.1.2
    table := chainValueTableOfList material.2.1
    values := tree.1
    cache := tree.2
  } : CoupledWarmedKeygenView), materialBaseHigh.1.2), materialBaseHigh.2)

structure CoupledWarmedKeygenCacheHighRelation
    (parameter : PublicParameter) (chain : ChainIndex)
    (left : CoupledWarmedKeygenView)
    (right : (CoupledWarmedKeygenView × (ChainValueIndex → Digest)) ×
      (ChainEdgeIndex → Digest)) : Prop where
  base : CoupledWarmedKeygenCacheRelation parameter chain left right.1
  highEq : chainEdgeHighTableOfCache left.cache parameter chain left.table =
    right.2

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledWarmedKeygenExperiment_withBaseHigh
    (parameter : PublicParameter) (chain : ChainIndex) :
    RelTriple
      (coupledWarmedKeygenExperiment parameter chain)
      (coupledWarmedKeygenWithBaseHigh parameter chain)
      (CoupledWarmedKeygenCacheHighRelation parameter chain) := by
  unfold coupledWarmedKeygenExperiment coupledWarmedKeygenWithBaseHigh
  apply relTriple_bind
    (relTriple_programmedWarmedTrajectoryMaterial_withBaseHigh parameter chain)
  intro leftMaterial rightMaterialBaseHigh hmaterial
  let rightMaterial := rightMaterialBaseHigh.1.1
  have hinvariant := warmedMaterialsAsFixed_invariant parameter chain
    leftMaterial rightMaterial rightMaterialBaseHigh.1.2
      hmaterial.leftSupport hmaterial.rightSupport hmaterial.tableEq
        hmaterial.outsideEq
  have htrees := relTriple_fixedChainMaterial_allTreeValues_root_and_paths
    parameter chain (warmedMaterialAsFixed chain leftMaterial)
      (warmedMaterialAsFixed chain rightMaterial,
        rightMaterialBaseHigh.1.2) hinvariant
  have htable := hinvariant.tableEq
  rw [fixedChainMaterialTable_warmedMaterialAsFixed parameter chain
    leftMaterial hmaterial.leftSupport] at htable
  apply relTriple_bind htrees
  intro leftTree rightTree htree
  apply relTriple_pure_pure
  refine ⟨?_, ?_⟩
  · refine ⟨⟨htable, ?_, htree.1, htree.2.1,
      htree.2.2.1, htree.2.2.2.1, htree.2.2.2.2.1⟩,
        htree.2.2.2.2.2.1⟩
    exact secretOutsideChain_eq_of_outsideChainSecret_eq chain
      leftMaterial.1.2 rightMaterial.1.2 hinvariant.outsideEq
  · have htrajectory := programmedWarmedTrajectoryMaterial_support_trajectory
      parameter chain leftMaterial hmaterial.leftSupport
    have hmatches := programmedFixedSeedChainTrajectories_edgesMatch parameter
      (unflattenSecret leftMaterial.1.2) chain leftMaterial.2 htrajectory
    calc
      chainEdgeHighTableOfCache leftTree.2 parameter chain
          (chainValueTableOfList leftMaterial.2.1) =
        chainEdgeHighTableOfCache leftMaterial.2.2 parameter chain
          (chainValueTableOfList leftMaterial.2.1) :=
        (chainEdgeHighTableOfCache_mono leftMaterial.2.2 leftTree.2 parameter
          chain (chainValueTableOfList leftMaterial.2.1) hmatches
            htree.2.2.2.2.2.2.1).symm
      _ = rightMaterialBaseHigh.2 := hmaterial.highEq

noncomputable def coupledWarmedFixedChainKeygenWithBaseHigh
    (chain : ChainIndex) :
    ProbComp ((ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let viewBaseHigh ← coupledWarmedKeygenWithBaseHigh parameter chain
  pure (((viewBaseHigh.1.1.toProgrammedView parameter, viewBaseHigh.1.2),
    viewBaseHigh.2))

set_option maxRecDepth 100000 in
theorem relTriple_coupledWarmedFixedChainKeygen_withBaseHigh
    (chain : ChainIndex) :
    RelTriple
      (coupledWarmedFixedChainKeygen chain)
      (coupledWarmedFixedChainKeygenWithBaseHigh chain)
      (ProgrammedActualKeygenCacheHighRelation chain) := by
  unfold coupledWarmedFixedChainKeygen
    coupledWarmedFixedChainKeygenWithBaseHigh
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledWarmedKeygenExperiment_withBaseHigh leftParameter chain)
  intro leftView rightView hview
  apply relTriple_pure_pure
  refine ⟨?_, ?_⟩
  · refine ⟨⟨hview.base.1.1, ?_, hview.base.1.2.1,
      hview.base.1.2.2.2.2.2.2⟩, hview.base.2⟩
    exact congrArg (fun root => PublicKey.mk root leftParameter)
      hview.base.1.2.2.2.2.2.1
  · simpa [CoupledWarmedKeygenView.toProgrammedView] using hview.highEq

theorem relTriple_programmedWarmedFixedChainKeygen_withBaseHigh
    (chain : ChainIndex) :
    RelTriple
      (programmedWarmedFixedChainKeygen chain)
      (coupledWarmedFixedChainKeygenWithBaseHigh chain)
      (ProgrammedActualKeygenCacheHighRelation chain) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_coupledWarmedFixedChainKeygen_eq_programmed chain).symm
  exact relTriple_coupledWarmedFixedChainKeygen_withBaseHigh chain

end XmssSecurity
