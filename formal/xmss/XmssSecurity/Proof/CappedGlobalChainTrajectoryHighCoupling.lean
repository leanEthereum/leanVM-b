import XmssSecurity.Proof.CappedGlobalChainEdgeHighUniformity
import XmssSecurity.Proof.CappedGlobalTreeCoupling
import XmssSecurity.Proof.ChainTrajectoryHighIndependence

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem programmedChainExtension_eq_root
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    programmedChainExtension parameter epoch chain step values cache =
      XmssSecurity.programmedChainExtension parameter epoch chain step values
        cache := by
  rfl

theorem programmedChainTrajectory_eq_root
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec),
    programmedChainTrajectory parameter epoch chain position steps value cache =
      XmssSecurity.programmedChainTrajectory parameter epoch chain position
        steps value cache := by
  intros
  rfl

theorem programmedFixedSeedChainTrajectories_eq_root
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) : ∀
      (cache : QueryCache HashSpec) (epochs : List Epoch),
    programmedFixedSeedChainTrajectoriesFromCache parameter secret chain steps
        cache epochs =
      XmssSecurity.programmedFixedSeedChainTrajectoriesFromCache parameter
        secret chain steps cache epochs := by
  intros
  rfl

abbrev AllChainHighRows := ChainIndex → List (ChainStep → Digest)

noncomputable def programmedAllChainTrajectoriesWithHigh
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    QueryCache HashSpec → List ChainIndex →
      ProbComp ((AllChainTrajectories × QueryCache HashSpec) ×
        AllChainHighRows)
  | cache, [] => pure ((fun _ => [], cache), fun _ => [])
  | cache, chain :: chains => do
      let first ←
        XmssSecurity.programmedFixedSeedChainTrajectoriesWithHigh parameter
          secret chain (chainLength - 1) cache allEpochs
      let rest ← programmedAllChainTrajectoriesWithHigh parameter secret
        first.1.2 chains
      pure ((Function.update rest.1.1 chain first.1.1, rest.1.2),
        Function.update rest.2 chain first.2)

@[simp]
theorem programmedAllChainTrajectoriesWithHigh_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) :
    programmedAllChainTrajectoriesWithHigh parameter secret cache [] =
      pure ((fun _ => [], cache), fun _ => []) := rfl

theorem programmedAllChainTrajectoriesWithHigh_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec) (chain : ChainIndex)
    (chains : List ChainIndex) :
    programmedAllChainTrajectoriesWithHigh parameter secret cache
      (chain :: chains) = (do
        let first ←
          XmssSecurity.programmedFixedSeedChainTrajectoriesWithHigh parameter
            secret chain (chainLength - 1) cache allEpochs
        let rest ← programmedAllChainTrajectoriesWithHigh parameter secret
          first.1.2 chains
        pure ((Function.update rest.1.1 chain first.1.1, rest.1.2),
          Function.update rest.2 chain first.2)) := rfl

def ProgrammedAllChainTrajectoriesHighRelation
    (parameter : PublicParameter) (chains : List ChainIndex)
    (initialCache : QueryCache HashSpec)
    (left : AllChainTrajectories × QueryCache HashSpec)
    (right : (AllChainTrajectories × QueryCache HashSpec) ×
      AllChainHighRows) : Prop :=
  left = right.1 ∧
    (∀ input,
      (∀ chain ∈ chains, ∀ epoch step value,
        input ≠ Concrete.CacheView.chainInput parameter epoch chain step value) →
      left.2 input = initialCache input) ∧
    ∀ chain ∈ chains,
      XmssSecurity.chainEdgeHighTableOfCache left.2 parameter chain
          (chainValueTableOfList (left.1 chain)) =
        XmssSecurity.chainEdgeHighTableOfRows (right.2 chain)

set_option maxRecDepth 100000 in
theorem relTriple_programmedAllChainTrajectories_exposes_high
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec),
      chains.Nodup → AllChainAddressesAbsent parameter chains cache →
      RelTriple
        (programmedAllChainTrajectoriesFromCache parameter secret cache chains)
        (programmedAllChainTrajectoriesWithHigh parameter secret cache chains)
        (ProgrammedAllChainTrajectoriesHighRelation parameter chains cache) := by
  intro chains
  induction chains with
  | nil =>
      intro cache _hnodup _habsent
      apply relTriple_pure_pure
      exact ⟨rfl, fun _input _hinput => rfl, by simp⟩
  | cons chain chains ih =>
      intro cache hnodup habsent
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [programmedAllChainTrajectoriesFromCache_cons,
        programmedAllChainTrajectoriesWithHigh_cons,
        programmedFixedSeedChainTrajectories_eq_root]
      apply relTriple_bind
        (XmssSecurity.relTriple_programmedFixedSeedChainTrajectories_exposes_high
          parameter secret chain (chainLength - 1) le_rfl allEpochs cache
            allEpochs_nodup)
      intro leftFirst rightFirst hfirst
      rcases hfirst with ⟨hfirstEq, hfirstPreserved, hfirstRows⟩
      subst leftFirst
      have htailAbsent : AllChainAddressesAbsent parameter chains
          rightFirst.1.2 := by
        intro later hlater epoch step input haddress
        rw [hfirstPreserved input]
        · exact habsent later (by simp [hlater]) epoch step input haddress
        · intro firstEpoch _hfirstEpoch firstStep value heq
          have hfirstAddress : AtHashAddress parameter
              (.chain firstEpoch chain firstStep) input := by
            rw [heq]
            unfold Concrete.CacheView.chainInput
            exact (atHashAddress_tweakableHashInput_iff parameter
              (.chain firstEpoch chain firstStep)
              (.chain firstEpoch chain firstStep)
              (Concrete.digestBytes value)).mpr rfl
          have hdomains := atHashAddress_unique parameter
            (.chain epoch later step) (.chain firstEpoch chain firstStep)
              input haddress hfirstAddress
          simp only [HashDomain.chain.injEq] at hdomains
          exact hnotMem (hdomains.2.1.symm ▸ hlater)
      apply relTriple_bind (ih rightFirst.1.2 htailNodup htailAbsent)
      intro leftRest rightRest hrest
      rcases hrest with ⟨hrestEq, hrestPreserved, hrestHigh⟩
      subst leftRest
      apply relTriple_pure_pure
      refine ⟨rfl, ?_, ?_⟩
      · intro input hinput
        calc
          rightRest.1.2 input = rightFirst.1.2 input := by
            exact hrestPreserved input (by
              intro later hlater epoch step value
              exact hinput later (by simp [hlater]) epoch step value)
          _ = cache input := by
            exact hfirstPreserved input (by
              intro epoch _hepoch step value
              exact hinput chain (by simp) epoch step value)
      · intro selected hselected
        rcases List.mem_cons.mp hselected with hselectedHead | hselectedTail
        · subst selected
          simp only [Function.update_self]
          have hcacheHigh :
              XmssSecurity.chainEdgeHighTableOfCache rightRest.1.2 parameter
                  chain (chainValueTableOfList rightFirst.1.1) =
                XmssSecurity.chainEdgeHighTableOfCache rightFirst.1.2
                  parameter chain (chainValueTableOfList rightFirst.1.1) := by
            funext edge
            unfold XmssSecurity.chainEdgeHighTableOfCache
            rw [hrestPreserved]
            intro later hlater epoch step value heq
            have hparts := (Concrete.CacheView.chainInput_eq_iff parameter
              edge.1 epoch chain later edge.2 step
                ((chainValueTableOfList rightFirst.1.1)
                  (edge.1, chainStepDigit edge.2)) value).mp heq
            exact hnotMem (hparts.2.1.symm ▸ hlater)
          rw [hcacheHigh]
          exact XmssSecurity.chainEdgeHighTableOfCache_eq_rows parameter chain
            rightFirst.1.1 rightFirst.1.2 rightFirst.2 hfirstRows
        · have hne : selected ≠ chain := by
            intro heq
            subst selected
            exact hnotMem hselectedTail
          simp only [Function.update_of_ne hne]
          exact hrestHigh selected hselectedTail

noncomputable def globalChainEdgeHighTableOfRows
    (rows : AllChainHighRows) : GlobalChainEdgeIndex → Digest := fun edge =>
  XmssSecurity.chainEdgeHighTableOfRows (rows edge.1) edge.2

theorem globalChainEdgeHighTableOfCache_eq_local
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (chain : ChainIndex) (edge : ChainEdgeIndex) :
    globalChainEdgeHighTableOfCache cache parameter table (chain, edge) =
      XmssSecurity.chainEdgeHighTableOfCache cache parameter chain
        (fun index => table (chain, index)) edge := by
  unfold globalChainEdgeHighTableOfCache
    XmssSecurity.chainEdgeHighTableOfCache
    globalChainTableEdgeInput XmssSecurity.chainTableEdgeInput
  have hdigit : chainStepDigit edge.2 =
      XmssSecurity.chainStepDigit edge.2 := by
    apply Fin.ext
    rfl
  rw [hdigit]
  simp only [XmssSecurity.hashOutputHigh]
  cases houtput : cache (Concrete.CacheView.chainInput parameter edge.1 chain
      edge.2 (table (chain, edge.1,
        XmssSecurity.chainStepDigit edge.2))) <;> simp

noncomputable def programmedGlobalChainTrajectoryMaterialWithHigh
    (parameter : PublicParameter) :
    ProbComp (GlobalChainTrajectoryMaterial ×
      (GlobalChainEdgeIndex → Digest)) := do
  let secret ← Concrete.sampleSecret
  let trajectoriesHigh ← programmedAllChainTrajectoriesWithHigh parameter
    secret ∅ allChains
  pure ((secret, trajectoriesHigh.1),
    globalChainEdgeHighTableOfRows trajectoriesHigh.2)

def ProgrammedGlobalChainTrajectoryMaterialHighRelation
    (parameter : PublicParameter)
    (left : GlobalChainTrajectoryMaterial)
    (right : GlobalChainTrajectoryMaterial ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  left = right.1 ∧
    globalChainEdgeHighTableOfCache left.2.2 parameter
        (globalChainTrajectoryMaterialTable left) = right.2

set_option maxRecDepth 100000 in
theorem relTriple_programmedGlobalChainTrajectoryMaterial_exposes_high
    (parameter : PublicParameter) :
    RelTriple
      (programmedGlobalChainTrajectoryMaterial parameter)
      (programmedGlobalChainTrajectoryMaterialWithHigh parameter)
      (ProgrammedGlobalChainTrajectoryMaterialHighRelation parameter) := by
  unfold programmedGlobalChainTrajectoryMaterial
    programmedGlobalChainTrajectoryMaterialWithHigh
  apply relTriple_bind (relTriple_refl Concrete.sampleSecret)
  intro leftSecret rightSecret hsecret
  subst rightSecret
  apply relTriple_bind
    (relTriple_programmedAllChainTrajectories_exposes_high parameter
      leftSecret allChains ∅ allChains_nodup (by
        simp [AllChainAddressesAbsent]))
  intro leftTrajectories rightTrajectories htrajectories
  apply relTriple_pure_pure
  refine ⟨congrArg (fun trajectories => (leftSecret, trajectories))
    htrajectories.1, ?_⟩
  funext edge
  rw [globalChainEdgeHighTableOfCache_eq_local]
  have hlocal := htrajectories.2.2 edge.1 (mem_allChains edge.1)
  exact congrFun hlocal edge.2

end XmssSecurity.CappedChain
