import XmssSecurity.CappedGlobalChainTrajectoryHighCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

attribute [local instance] XmssSecurity.presamplingSampleableChainEdges

noncomputable local instance globalTrajectoryHighUniformCurriedTable :
    SampleableType (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest) :=
  SampleableType.ofFintype
    (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)

noncomputable local instance globalTrajectoryHighUniformGlobalTable :
    SampleableType (GlobalChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainEdgeIndex → Digest)

noncomputable def programmedAllChainTrajectoryValuesHigh
    (secret : Epoch → ChainIndex → Digest) :
    List ChainIndex → ProbComp (AllChainTrajectories × AllChainHighRows)
  | [] => pure (fun _ => [], fun _ => [])
  | chain :: chains => do
      let trajectories ← XmssSecurity.programmedFixedSeedChainValues secret
        chain (chainLength - 1) allEpochs
      let highs ← XmssSecurity.sampleChainHighRows (chainLength - 1)
        allEpochs.length
      let rest ← programmedAllChainTrajectoryValuesHigh secret chains
      pure (Function.update rest.1 chain trajectories,
        Function.update rest.2 chain highs)

@[simp]
theorem programmedAllChainTrajectoryValuesHigh_nil
    (secret : Epoch → ChainIndex → Digest) :
    programmedAllChainTrajectoryValuesHigh secret [] =
      pure (fun _ => [], fun _ => []) := rfl

theorem programmedAllChainTrajectoryValuesHigh_cons
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (chains : List ChainIndex) :
    programmedAllChainTrajectoryValuesHigh secret (chain :: chains) = (do
      let trajectories ← XmssSecurity.programmedFixedSeedChainValues secret
        chain (chainLength - 1) allEpochs
      let highs ← XmssSecurity.sampleChainHighRows (chainLength - 1)
        allEpochs.length
      let rest ← programmedAllChainTrajectoryValuesHigh secret chains
      pure (Function.update rest.1 chain trajectories,
        Function.update rest.2 chain highs)) := rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_programmedAllChainTrajectoriesWithHigh_values_high
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec),
    evalDist ((fun result => (result.1.1, result.2)) <$>
      programmedAllChainTrajectoriesWithHigh parameter secret cache chains) =
    evalDist (programmedAllChainTrajectoryValuesHigh secret chains) := by
  intro chains
  induction chains with
  | nil =>
      intro cache
      simp
  | cons chain chains ih =>
      intro cache
      rw [programmedAllChainTrajectoriesWithHigh_cons,
        programmedAllChainTrajectoryValuesHigh_cons]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      let finish := fun first :
          (List FullChainTrajectory × QueryCache HashSpec) ×
            List (ChainStep → Digest) =>
        programmedAllChainTrajectoryValuesHigh secret chains >>= fun rest =>
          pure (Function.update rest.1 chain first.1.1,
            Function.update rest.2 chain first.2)
      calc
        evalDist (XmssSecurity.programmedFixedSeedChainTrajectoriesWithHigh
            parameter secret chain (chainLength - 1) cache allEpochs >>=
          fun first =>
            programmedAllChainTrajectoriesWithHigh parameter secret
                first.1.2 chains >>= fun rest =>
              pure (Function.update rest.1.1 chain first.1.1,
                Function.update rest.2 chain first.2)) =
          evalDist (XmssSecurity.programmedFixedSeedChainTrajectoriesWithHigh
              parameter secret chain (chainLength - 1) cache allEpochs >>=
            finish) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          unfold finish
          calc
            _ = evalDist (((fun result => (result.1.1, result.2)) <$>
                  programmedAllChainTrajectoriesWithHigh parameter secret
                    first.1.2 chains) >>= fun rest =>
                pure (Function.update rest.1 chain first.1.1,
                  Function.update rest.2 chain first.2)) := by
              simp [map_eq_bind_pure_comp, bind_assoc]
            _ = _ := by
              rw [evalDist_bind, ih first.1.2, ← evalDist_bind]
        _ = evalDist (((fun first => (first.1.1, first.2)) <$>
              XmssSecurity.programmedFixedSeedChainTrajectoriesWithHigh
                parameter secret chain (chainLength - 1) cache allEpochs) >>=
            fun first =>
              programmedAllChainTrajectoryValuesHigh secret chains >>=
                fun rest =>
              pure (Function.update rest.1 chain first.1,
                Function.update rest.2 chain first.2)) := by
          simp [finish, map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist ((do
              let trajectories ← XmssSecurity.programmedFixedSeedChainValues
                secret chain (chainLength - 1) allEpochs
              let highs ← XmssSecurity.sampleChainHighRows
                (chainLength - 1) allEpochs.length
              pure (trajectories, highs)) >>= fun first =>
            programmedAllChainTrajectoryValuesHigh secret chains >>= fun rest =>
              pure (Function.update rest.1 chain first.1,
                Function.update rest.2 chain first.2)) := by
          rw [evalDist_bind,
            XmssSecurity.evalDist_programmedFixedSeedChainTrajectoriesWithHigh_values_high
              parameter secret chain (chainLength - 1) le_rfl allEpochs cache,
            ← evalDist_bind]
        _ = evalDist (programmedAllChainTrajectoryValuesHigh secret
              (chain :: chains)) := by
          rw [programmedAllChainTrajectoryValuesHigh_cons]
          simp [bind_assoc]

noncomputable def programmedAllChainTrajectoryValues
    (secret : Epoch → ChainIndex → Digest) :
    List ChainIndex → ProbComp AllChainTrajectories
  | [] => pure (fun _ => [])
  | chain :: chains => do
      let trajectories ← XmssSecurity.programmedFixedSeedChainValues secret
        chain (chainLength - 1) allEpochs
      let rest ← programmedAllChainTrajectoryValues secret chains
      pure (Function.update rest chain trajectories)

noncomputable def sampleAllChainHighRows :
    List ChainIndex → ProbComp AllChainHighRows
  | [] => pure (fun _ => [])
  | chain :: chains => do
      let highs ← XmssSecurity.sampleChainHighRows (chainLength - 1)
        allEpochs.length
      let rest ← sampleAllChainHighRows chains
      pure (Function.update rest chain highs)

@[simp]
theorem programmedAllChainTrajectoryValues_nil
    (secret : Epoch → ChainIndex → Digest) :
    programmedAllChainTrajectoryValues secret [] = pure (fun _ => []) := rfl

theorem programmedAllChainTrajectoryValues_cons
    (secret : Epoch → ChainIndex → Digest) (chain : ChainIndex)
    (chains : List ChainIndex) :
    programmedAllChainTrajectoryValues secret (chain :: chains) = (do
      let trajectories ← XmssSecurity.programmedFixedSeedChainValues secret
        chain (chainLength - 1) allEpochs
      let rest ← programmedAllChainTrajectoryValues secret chains
      pure (Function.update rest chain trajectories)) := rfl

@[simp]
theorem sampleAllChainHighRows_nil :
    sampleAllChainHighRows [] = pure (fun _ => []) := rfl

theorem sampleAllChainHighRows_cons
    (chain : ChainIndex) (chains : List ChainIndex) :
    sampleAllChainHighRows (chain :: chains) = (do
      let highs ← XmssSecurity.sampleChainHighRows (chainLength - 1)
        allEpochs.length
      let rest ← sampleAllChainHighRows chains
      pure (Function.update rest chain highs)) := rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_programmedAllChainTrajectoryValuesHigh_eq_independent
    (secret : Epoch → ChainIndex → Digest) : ∀ chains : List ChainIndex,
    evalDist (programmedAllChainTrajectoryValuesHigh secret chains) =
    evalDist (do
      let trajectories ← programmedAllChainTrajectoryValues secret chains
      let highs ← sampleAllChainHighRows chains
      pure (trajectories, highs)) := by
  intro chains
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      rw [programmedAllChainTrajectoryValuesHigh_cons,
        programmedAllChainTrajectoryValues_cons, sampleAllChainHighRows_cons]
      calc
        _ = evalDist (do
            let trajectories ← XmssSecurity.programmedFixedSeedChainValues
              secret chain (chainLength - 1) allEpochs
            let highs ← XmssSecurity.sampleChainHighRows
              (chainLength - 1) allEpochs.length
            let restTrajectories ←
              programmedAllChainTrajectoryValues secret chains
            let restHighs ← sampleAllChainHighRows chains
            pure (Function.update restTrajectories chain trajectories,
              Function.update restHighs chain highs)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro trajectories
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro highs
          calc
            _ = evalDist (programmedAllChainTrajectoryValuesHigh secret chains >>=
                fun rest =>
                pure (Function.update rest.1 chain trajectories,
                  Function.update rest.2 chain highs)) := by rfl
            _ = evalDist ((do
                  let restTrajectories ←
                    programmedAllChainTrajectoryValues secret chains
                  let restHighs ← sampleAllChainHighRows chains
                  pure (restTrajectories, restHighs)) >>= fun rest =>
                pure (Function.update rest.1 chain trajectories,
                  Function.update rest.2 chain highs)) := by
              rw [evalDist_bind, ih, ← evalDist_bind]
            _ = _ := by simp
        _ = evalDist (do
            let trajectories ← XmssSecurity.programmedFixedSeedChainValues
              secret chain (chainLength - 1) allEpochs
            let restTrajectories ←
              programmedAllChainTrajectoryValues secret chains
            let highs ← XmssSecurity.sampleChainHighRows
              (chainLength - 1) allEpochs.length
            let restHighs ← sampleAllChainHighRows chains
            pure (Function.update restTrajectories chain trajectories,
              Function.update restHighs chain highs)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro trajectories
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            (XmssSecurity.sampleChainHighRows
              (chainLength - 1) allEpochs.length)
            (programmedAllChainTrajectoryValues secret chains)
            (fun highs restTrajectories =>
              sampleAllChainHighRows chains >>= fun restHighs =>
              pure (Function.update restTrajectories chain trajectories,
                Function.update restHighs chain highs))
        _ = _ := by simp [bind_assoc]

theorem evalDist_programmedFixedSeedChainValues_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1)
    (epochs : List Epoch)
    (cache : QueryCache HashSpec) :
    evalDist (XmssSecurity.programmedFixedSeedChainValues secret chain steps
      epochs) =
    evalDist (uniformFixedChainTrajectories secret chain steps epochs) := by
  calc
    _ = evalDist (Prod.fst <$>
        XmssSecurity.programmedFixedSeedChainTrajectoriesFromCache parameter
          secret chain steps cache epochs) :=
      (XmssSecurity.evalDist_programmedFixedSeedChainTrajectories_values
        parameter secret chain steps epochs cache).symm
    _ = evalDist (Prod.fst <$>
        programmedFixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) := by
      rw [programmedFixedSeedChainTrajectories_eq_root]
    _ = _ := evalDist_programmedFixedChainTrajectories_fst_eq_uniform
      parameter secret chain steps hsteps epochs cache

set_option maxRecDepth 100000 in
theorem evalDist_programmedAllChainTrajectoryValues_eq_uniform
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ chains : List ChainIndex,
    evalDist (programmedAllChainTrajectoryValues secret chains) =
    evalDist (uniformAllChainTrajectories secret chains) := by
  intro chains
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      rw [programmedAllChainTrajectoryValues_cons,
        uniformAllChainTrajectories_cons]
      calc
        _ = evalDist (uniformFixedChainTrajectories secret chain
              (chainLength - 1) allEpochs >>= fun trajectories =>
            programmedAllChainTrajectoryValues secret chains >>= fun rest =>
              pure (Function.update rest chain trajectories)) := by
          rw [evalDist_bind,
            evalDist_programmedFixedSeedChainValues_eq_uniform parameter secret
              chain (chainLength - 1) le_rfl allEpochs ∅,
            ← evalDist_bind]
        _ = _ := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro trajectories
          rw [evalDist_bind, ih, ← evalDist_bind]

noncomputable def allChainHighTableOfRows
    (rows : AllChainHighRows) :
    ChainIndex → XmssSecurity.ChainEdgeIndex → Digest :=
  fun chain => XmssSecurity.chainEdgeHighTableOfRows (rows chain)

def uncurryGlobalChainEdgeTable
    (table : ChainIndex → XmssSecurity.ChainEdgeIndex → Digest) :
    GlobalChainEdgeIndex → Digest := fun edge => table edge.1 edge.2

noncomputable def updateChainHighTable
    (table : ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
    (chain : ChainIndex) (high : XmssSecurity.ChainEdgeIndex → Digest) :
    ChainIndex → XmssSecurity.ChainEdgeIndex → Digest :=
  Function.update table chain high

noncomputable def patchAllChainHighTable :
    List ChainIndex →
      ProbComp (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
  | [] => pure (fun _chain _edge => 0)
  | chain :: chains => do
      let rest ← patchAllChainHighTable chains
      let high ← @uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
        XmssSecurity.presamplingSampleableChainEdges
      pure (updateChainHighTable rest chain high)

@[simp]
theorem patchAllChainHighTable_nil :
    patchAllChainHighTable [] = pure (fun _chain _edge => 0) := rfl

theorem patchAllChainHighTable_cons
    (chain : ChainIndex) (chains : List ChainIndex) :
    patchAllChainHighTable (chain :: chains) = (do
      let rest ← patchAllChainHighTable chains
      let high ← @uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
        XmssSecurity.presamplingSampleableChainEdges
      pure (updateChainHighTable rest chain high)) := rfl

theorem globalChainEdgeHighTableOfRows_eq_uncurry
    (rows : AllChainHighRows) :
    globalChainEdgeHighTableOfRows rows =
      uncurryGlobalChainEdgeTable (allChainHighTableOfRows rows) := rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_sampleAllChainHighRows_table_eq_patch :
    ∀ chains : List ChainIndex,
    evalDist (allChainHighTableOfRows <$> sampleAllChainHighRows chains) =
    evalDist (patchAllChainHighTable chains) := by
  intro chains
  induction chains with
  | nil =>
      simp only [sampleAllChainHighRows_nil, map_pure,
        patchAllChainHighTable_nil]
      congr 2
      funext chain edge
      unfold allChainHighTableOfRows
        XmssSecurity.chainEdgeHighTableOfRows
      rw [dif_neg]
      simp [allEpochs_length, lifetime, treeHeight]
  | cons chain chains ih =>
      rw [sampleAllChainHighRows_cons, patchAllChainHighTable_cons]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      calc
        _ = evalDist (XmssSecurity.sampleChainHighRows (chainLength - 1)
              allEpochs.length >>= fun rows =>
            sampleAllChainHighRows chains >>= fun rest =>
              pure (updateChainHighTable (allChainHighTableOfRows rest) chain
                (XmssSecurity.chainEdgeHighTableOfRows rows))) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro rows
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro rest
          congr 2
          unfold updateChainHighTable
          funext selected
          by_cases heq : selected = chain
          · subst selected
            simp [allChainHighTableOfRows]
          · simp [allChainHighTableOfRows, Function.update_of_ne heq]
        _ = evalDist ((XmssSecurity.chainEdgeHighTableOfRows <$>
              XmssSecurity.sampleChainHighRows (chainLength - 1)
                allEpochs.length) >>= fun high =>
            (allChainHighTableOfRows <$> sampleAllChainHighRows chains) >>=
              fun rest => pure (updateChainHighTable rest chain high)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist ((@uniformSample
              (XmssSecurity.ChainEdgeIndex → Digest)
              XmssSecurity.presamplingSampleableChainEdges) >>= fun high =>
            (allChainHighTableOfRows <$> sampleAllChainHighRows chains) >>=
              fun rest => pure (updateChainHighTable rest chain high)) := by
          rw [evalDist_bind,
            XmssSecurity.evalDist_chainEdgeHighTableOfRows_sample_eq_uniform,
            ← evalDist_bind]
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist ((@uniformSample
              (XmssSecurity.ChainEdgeIndex → Digest)
              XmssSecurity.presamplingSampleableChainEdges) >>= fun high =>
            patchAllChainHighTable chains >>= fun rest =>
              pure (updateChainHighTable rest chain high)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro high
          rw [evalDist_bind, ih, ← evalDist_bind]
        _ = evalDist (patchAllChainHighTable chains >>= fun rest =>
            (@uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
              XmssSecurity.presamplingSampleableChainEdges) >>= fun high =>
              pure (updateChainHighTable rest chain high)) :=
          OracleComp.DeferredSampling.evalDist_bind_comm
            (@uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
              XmssSecurity.presamplingSampleableChainEdges)
            (patchAllChainHighTable chains)
            (fun high rest => pure (updateChainHighTable rest chain high))
        _ = _ := by rfl

noncomputable def patchAllChainHighTableFrom
    (base : ChainIndex → XmssSecurity.ChainEdgeIndex → Digest) :
    List ChainIndex →
      ProbComp (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
  | [] => pure base
  | chain :: chains => do
      let rest ← patchAllChainHighTableFrom base chains
      let high ← @uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
        XmssSecurity.presamplingSampleableChainEdges
      pure (updateChainHighTable rest chain high)

@[simp]
theorem patchAllChainHighTableFrom_nil
    (base : ChainIndex → XmssSecurity.ChainEdgeIndex → Digest) :
    patchAllChainHighTableFrom base [] = pure base := rfl

theorem patchAllChainHighTableFrom_cons
    (base : ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
    (chain : ChainIndex) (chains : List ChainIndex) :
    patchAllChainHighTableFrom base (chain :: chains) = (do
      let rest ← patchAllChainHighTableFrom base chains
      let high ← @uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
        XmssSecurity.presamplingSampleableChainEdges
      pure (updateChainHighTable rest chain high)) := rfl

def PatchedChainHighTablesRelation
    (chains : List ChainIndex)
    (leftBase rightBase : ChainIndex →
      XmssSecurity.ChainEdgeIndex → Digest)
    (left right : ChainIndex →
      XmssSecurity.ChainEdgeIndex → Digest) : Prop :=
  (∀ chain ∈ chains, left chain = right chain) ∧
    ∀ chain, chain ∉ chains →
      left chain = leftBase chain ∧ right chain = rightBase chain

theorem relTriple_patchAllChainHighTableFrom
    (leftBase rightBase : ChainIndex →
      XmssSecurity.ChainEdgeIndex → Digest) :
    ∀ chains : List ChainIndex,
    RelTriple
      (patchAllChainHighTableFrom leftBase chains)
      (patchAllChainHighTableFrom rightBase chains)
      (PatchedChainHighTablesRelation chains leftBase rightBase) := by
  intro chains
  induction chains with
  | nil =>
      apply relTriple_pure_pure
      exact ⟨by simp, fun chain _hchain => ⟨rfl, rfl⟩⟩
  | cons chain chains ih =>
      rw [patchAllChainHighTableFrom_cons,
        patchAllChainHighTableFrom_cons]
      apply relTriple_bind ih
      intro leftRest rightRest hrest
      apply relTriple_bind (relTriple_refl
        (@uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
          XmssSecurity.presamplingSampleableChainEdges))
      intro leftHigh rightHigh hhigh
      subst rightHigh
      apply relTriple_pure_pure
      constructor
      · intro selected hselected
        by_cases heq : selected = chain
        · subst selected
          simp [updateChainHighTable]
        · have htail : selected ∈ chains := by
            simpa [heq] using hselected
          unfold updateChainHighTable
          simp only [Function.update_of_ne heq]
          exact hrest.1 selected htail
      · intro selected hselected
        have hne : selected ≠ chain := by
          intro heq
          subst selected
          exact hselected (by simp)
        have houtside : selected ∉ chains := by
          intro htail
          exact hselected (by simp [htail])
        obtain ⟨hleft, hright⟩ := hrest.2 selected houtside
        unfold updateChainHighTable
        simp only [Function.update_of_ne hne]
        exact ⟨hleft, hright⟩

set_option maxRecDepth 1000000 in
theorem evalDist_patchAllChainHighTableFrom_uniform
    (chains : List ChainIndex) :
    evalDist (do
      let base ← $ᵗ
        (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
      patchAllChainHighTableFrom base chains) =
    evalDist ($ᵗ
      (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)) := by
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      calc
        evalDist (do
            let base ← $ᵗ
              (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
            patchAllChainHighTableFrom base (chain :: chains)) =
          evalDist ((do
              let base ← $ᵗ
                (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
              patchAllChainHighTableFrom base chains) >>= fun rest =>
            (@uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
              XmssSecurity.presamplingSampleableChainEdges) >>= fun high =>
              pure (updateChainHighTable rest chain high)) := by
          simp [patchAllChainHighTableFrom_cons, bind_assoc]
        _ = evalDist (($ᵗ
              (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)) >>=
            fun rest =>
            (@uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
              XmssSecurity.presamplingSampleableChainEdges) >>= fun high =>
              pure (updateChainHighTable rest chain high)) := by
          rw [evalDist_bind, ih, ← evalDist_bind]
        _ = evalDist ((@uniformSample
              (XmssSecurity.ChainEdgeIndex → Digest)
              XmssSecurity.presamplingSampleableChainEdges) >>= fun high =>
            ($ᵗ
              (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)) >>=
                fun rest => pure (updateChainHighTable rest chain high)) :=
          OracleComp.DeferredSampling.evalDist_bind_comm
            ($ᵗ
              (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest))
            (@uniformSample (XmssSecurity.ChainEdgeIndex → Digest)
              XmssSecurity.presamplingSampleableChainEdges)
            (fun rest high => pure (updateChainHighTable rest chain high))
        _ = _ := by
          unfold updateChainHighTable
          exact evalDist_uniformSample_bind_update chain

theorem patchAllChainHighTable_eq_from_zero : ∀ chains : List ChainIndex,
    patchAllChainHighTable chains =
      patchAllChainHighTableFrom (fun _chain _edge => 0) chains := by
  intro chains
  induction chains with
  | nil => rfl
  | cons chain chains ih =>
      rw [patchAllChainHighTable_cons, patchAllChainHighTableFrom_cons, ih]

theorem evalDist_patchAllChainHighTableFrom_allChains_eq
    (leftBase rightBase : ChainIndex →
      XmssSecurity.ChainEdgeIndex → Digest) :
    evalDist (patchAllChainHighTableFrom leftBase allChains) =
    evalDist (patchAllChainHighTableFrom rightBase allChains) := by
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_post_mono
    (relTriple_patchAllChainHighTableFrom leftBase rightBase allChains)
  intro left right hrel
  funext chain
  exact hrel.1 chain (mem_allChains chain)

set_option maxRecDepth 1000000 in
theorem evalDist_patchAllChainHighTable_allChains_eq_uniform :
    evalDist (patchAllChainHighTable allChains) =
    evalDist ($ᵗ
      (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)) := by
  rw [patchAllChainHighTable_eq_from_zero]
  let zero : ChainIndex → XmssSecurity.ChainEdgeIndex → Digest :=
    fun _chain _edge => 0
  calc
    evalDist (patchAllChainHighTableFrom zero allChains) =
        evalDist (do
          let base ← $ᵗ
            (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
          patchAllChainHighTableFrom base allChains) := by
      symm
      calc
        _ = evalDist (($ᵗ
              (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)) >>=
            fun _base => patchAllChainHighTableFrom zero allChains) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro base
          exact (evalDist_patchAllChainHighTableFrom_allChains_eq base zero)
        _ = evalDist (patchAllChainHighTableFrom zero allChains) :=
          OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            ($ᵗ (ChainIndex →
              XmssSecurity.ChainEdgeIndex → Digest))
            (probFailure_eq_zero' inferInstance)
            (patchAllChainHighTableFrom zero allChains)
    _ = _ := evalDist_patchAllChainHighTableFrom_uniform allChains

noncomputable def globalChainEdgeTableCurryEquiv :
    (GlobalChainEdgeIndex → Digest) ≃
      (ChainIndex → XmssSecurity.ChainEdgeIndex → Digest) :=
  Equiv.curry ChainIndex XmssSecurity.ChainEdgeIndex Digest

theorem globalChainEdgeTableCurryEquiv_symm_eq_uncurry :
    globalChainEdgeTableCurryEquiv.symm = uncurryGlobalChainEdgeTable := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_uncurry_patchAllChainHighTable_eq_uniform :
    evalDist (uncurryGlobalChainEdgeTable <$>
      patchAllChainHighTable allChains) =
    evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    _ = evalDist (uncurryGlobalChainEdgeTable <$>
        ($ᵗ (ChainIndex →
          XmssSecurity.ChainEdgeIndex → Digest))) := by
      rw [evalDist_map,
        evalDist_patchAllChainHighTable_allChains_eq_uniform,
        ← evalDist_map]
    _ = _ := by
      rw [← globalChainEdgeTableCurryEquiv_symm_eq_uncurry]
      exact evalDist_map_bijective_uniform_cross
        (α := ChainIndex → XmssSecurity.ChainEdgeIndex → Digest)
        (β := GlobalChainEdgeIndex → Digest)
        globalChainEdgeTableCurryEquiv.symm
        globalChainEdgeTableCurryEquiv.symm.bijective

set_option maxRecDepth 1000000 in
theorem evalDist_sampleAllChainHighRows_globalTable_eq_uniform :
    evalDist (globalChainEdgeHighTableOfRows <$>
      sampleAllChainHighRows allChains) =
    evalDist ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    _ = evalDist (uncurryGlobalChainEdgeTable <$>
        (allChainHighTableOfRows <$>
          sampleAllChainHighRows allChains)) := by
      simp only [Functor.map_map]
      congr 2
    _ = evalDist (uncurryGlobalChainEdgeTable <$>
        patchAllChainHighTable allChains) := by
      rw [evalDist_map, evalDist_sampleAllChainHighRows_table_eq_patch,
        ← evalDist_map]
    _ = _ := evalDist_uncurry_patchAllChainHighTable_eq_uniform

noncomputable def programmedGlobalChainTrajectoryTableHighView
    (parameter : PublicParameter) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :=
  (fun materialHigh =>
    (globalChainTrajectoryMaterialTable materialHigh.1, materialHigh.2)) <$>
      programmedGlobalChainTrajectoryMaterialWithHigh parameter

noncomputable def independentGlobalChainValueTable :
    ProbComp (GlobalChainValueIndex → Digest) :=
  $ᵗ (GlobalChainValueIndex → Digest)

noncomputable def independentGlobalChainHigh :
    ProbComp (GlobalChainEdgeIndex → Digest) :=
  $ᵗ (GlobalChainEdgeIndex → Digest)

noncomputable def independentGlobalChainTableHigh :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let table ← independentGlobalChainValueTable
  let high ← independentGlobalChainHigh
  pure (table, high)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedAllChainTrajectoriesWithHigh_tableHigh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    evalDist (programmedAllChainTrajectoriesWithHigh parameter secret ∅
        allChains >>= fun trajectoriesHigh =>
      pure (globalChainValueTableOfTrajectories trajectoriesHigh.1.1,
        globalChainEdgeHighTableOfRows trajectoriesHigh.2)) =
    evalDist (uniformAllChainTrajectories secret allChains >>=
      fun trajectories =>
      ($ᵗ (GlobalChainEdgeIndex → Digest)) >>= fun high =>
      pure (globalChainValueTableOfTrajectories trajectories, high)) := by
  let finish := fun result : AllChainTrajectories × AllChainHighRows =>
    (globalChainValueTableOfTrajectories result.1,
      globalChainEdgeHighTableOfRows result.2)
  calc
    evalDist (programmedAllChainTrajectoriesWithHigh parameter secret ∅
          allChains >>= fun trajectoriesHigh =>
        pure (globalChainValueTableOfTrajectories trajectoriesHigh.1.1,
          globalChainEdgeHighTableOfRows trajectoriesHigh.2)) =
      evalDist (finish <$>
        ((fun result => (result.1.1, result.2)) <$>
          programmedAllChainTrajectoriesWithHigh parameter secret ∅
            allChains)) := by
        simp [finish, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (finish <$>
        programmedAllChainTrajectoryValuesHigh secret allChains) := by
      rw [evalDist_map,
        evalDist_programmedAllChainTrajectoriesWithHigh_values_high,
        ← evalDist_map]
    _ = evalDist (finish <$> (do
        let trajectories ← programmedAllChainTrajectoryValues secret allChains
        let highs ← sampleAllChainHighRows allChains
        pure (trajectories, highs))) := by
      rw [evalDist_map,
        evalDist_programmedAllChainTrajectoryValuesHigh_eq_independent,
        ← evalDist_map]
    _ = evalDist (programmedAllChainTrajectoryValues secret allChains >>=
        fun trajectories =>
        (globalChainEdgeHighTableOfRows <$>
          sampleAllChainHighRows allChains) >>= fun high =>
        pure (globalChainValueTableOfTrajectories trajectories, high)) := by
      simp [finish, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (uniformAllChainTrajectories secret allChains >>=
        fun trajectories =>
        (globalChainEdgeHighTableOfRows <$>
          sampleAllChainHighRows allChains) >>= fun high =>
        pure (globalChainValueTableOfTrajectories trajectories, high)) := by
      rw [evalDist_bind,
        evalDist_programmedAllChainTrajectoryValues_eq_uniform parameter
          secret allChains,
        ← evalDist_bind]
    _ = evalDist (uniformAllChainTrajectories secret allChains >>=
        fun trajectories =>
        ($ᵗ (GlobalChainEdgeIndex → Digest)) >>= fun high =>
        pure (globalChainValueTableOfTrajectories trajectories, high)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro trajectories
      rw [evalDist_bind,
        evalDist_sampleAllChainHighRows_globalTable_eq_uniform,
        ← evalDist_bind]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_programmedGlobalChainTrajectoryTableHighView_eq_independent
    (parameter : PublicParameter) :
    evalDist (programmedGlobalChainTrajectoryTableHighView parameter) =
    evalDist independentGlobalChainTableHigh := by
  unfold programmedGlobalChainTrajectoryTableHighView
    programmedGlobalChainTrajectoryMaterialWithHigh
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  let appendHigh := fun table : GlobalChainValueIndex → Digest =>
    ($ᵗ (GlobalChainEdgeIndex → Digest)) >>= fun high =>
      pure (table, high)
  calc
    _ = evalDist (Concrete.sampleSecret >>= fun secret =>
        uniformAllChainTrajectories secret allChains >>= fun trajectories =>
        ($ᵗ (GlobalChainEdgeIndex → Digest)) >>= fun high =>
        pure (globalChainValueTableOfTrajectories trajectories, high)) := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro secret
      exact evalDist_programmedAllChainTrajectoriesWithHigh_tableHigh
        parameter secret
    _ = evalDist (uniformGlobalChainTableFromTrajectories >>= appendHigh) := by
      simp [uniformGlobalChainTableFromTrajectories, appendHigh,
        map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (independentGlobalChainValueTable >>=
        appendHigh) := by
      rw [evalDist_bind,
        evalDist_uniformGlobalChainTableFromTrajectories_eq_uniform,
        ← evalDist_bind]
      unfold independentGlobalChainValueTable
      rfl
    _ = _ := by rfl

noncomputable def programmedGlobalChainTrajectoryCacheTableHighView
    (parameter : PublicParameter) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :=
  (fun material =>
    (globalChainTrajectoryMaterialTable material,
      globalChainEdgeHighTableOfCache material.2.2 parameter
        (globalChainTrajectoryMaterialTable material))) <$>
      programmedGlobalChainTrajectoryMaterial parameter

set_option maxRecDepth 1000000 in
theorem evalDist_programmedGlobalChainTrajectoryCacheTableHighView_eq_independent
    (parameter : PublicParameter) :
    evalDist (programmedGlobalChainTrajectoryCacheTableHighView parameter) =
    evalDist independentGlobalChainTableHigh := by
  let leftView := fun material : GlobalChainTrajectoryMaterial =>
    (globalChainTrajectoryMaterialTable material,
      globalChainEdgeHighTableOfCache material.2.2 parameter
        (globalChainTrajectoryMaterialTable material))
  let rightView := fun materialHigh : GlobalChainTrajectoryMaterial ×
      (GlobalChainEdgeIndex → Digest) =>
    (globalChainTrajectoryMaterialTable materialHigh.1, materialHigh.2)
  have hcoupling := relTriple_post_mono
    (relTriple_programmedGlobalChainTrajectoryMaterial_exposes_high parameter)
    (fun left right hrel => show leftView left = rightView right by
      unfold leftView rightView
      apply Prod.ext
      · exact congrArg globalChainTrajectoryMaterialTable hrel.1
      · exact hrel.2)
  calc
    evalDist (programmedGlobalChainTrajectoryCacheTableHighView parameter) =
      evalDist (rightView <$>
        programmedGlobalChainTrajectoryMaterialWithHigh parameter) := by
      unfold programmedGlobalChainTrajectoryCacheTableHighView
      exact evalDist_map_eq_of_relTriple hcoupling
    _ = evalDist (programmedGlobalChainTrajectoryTableHighView parameter) := by
      rfl
    _ = _ :=
      evalDist_programmedGlobalChainTrajectoryTableHighView_eq_independent
        parameter

end XmssSecurity.CappedChain
