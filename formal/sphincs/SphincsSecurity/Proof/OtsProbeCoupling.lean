import SphincsSecurity.Proof.OtsProbeTrace
import SphincsSecurity.Proof.FtsProbeProbability

/-!
# Retained one-time game coupling

The ordinary side of the split probing oracle is exactly the real lazy random oracle. This module
packages that distributional identity as the relational kernel used by the retained-game lift.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def RawOrdinaryResultRel :
    LazyRevealProbe.RawResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done _ _ (value, cache), ordinaryResult =>
      ordinaryResult = (value, ordinaryQueryCache cache)

def RawOrdinaryResultRelAt
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    LazyRevealProbe.RawResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done finalState remaining (value, cache), ordinaryResult =>
      finalState = state ∧ remaining = fuel ∧
        ordinaryResult = (value, ordinaryQueryCache cache)

theorem exists_right_mem_support_of_relTriple
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {left : OracleComp spec₁ alpha} {right : OracleComp spec₂ beta}
    {relation : alpha → beta → Prop}
    (hrel : RelTriple left right relation) {leftResult : alpha}
    (hleft : leftResult ∈ support left) :
    ∃ rightResult ∈ support right, relation leftResult rightResult := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel
  obtain ⟨coupling, hcoupled⟩ := hrel
  have hleftEval : leftResult ∈ support 𝒟[left] := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hleft ⊢
    exact hleft
  have hleftMapped : leftResult ∈ support (Prod.fst <$> coupling.1) := by
    rw [coupling.2.map_fst]
    exact hleftEval
  rw [support_map] at hleftMapped
  obtain ⟨jointResult, hjoint, hfst⟩ := hleftMapped
  rcases jointResult with ⟨coupledLeft, coupledRight⟩
  simp only at hfst
  subst coupledLeft
  refine ⟨coupledRight, ?_, hcoupled (leftResult, coupledRight) hjoint⟩
  have hrightMapped : coupledRight ∈ support (Prod.snd <$> coupling.1) := by
    rw [support_map]
    exact ⟨(leftResult, coupledRight), hjoint, rfl⟩
  rw [coupling.2.map_snd] at hrightMapped
  rw [mem_support_iff_evalDist_apply_ne_zero] at hrightMapped ⊢
  exact hrightMapped

theorem probingHashQuery_eq_splitHashQuery_of_stable
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    probingHashQuery parameter input = splitHashQuery (.ordinary input) := by
  unfold probingHashQuery
  rw [hstable.1]
  cases hposition : decodePosition? parameter input with
  | none => rfl
  | some position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | leaf lay tree leafIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | node lay tree level nodeIdx =>
          exact (hstable.2 _ hposition (by trivial)).elim
      | ftsLeaf | ftsNode | ftsRoots => rfl

theorem probingHashImpl_eq_ordinaryHashImpl_of_stable
    (parameter : PublicParameter) (input : HashInput)
    (hstable : StableOrdinaryInput parameter input) :
    probingHashImpl parameter input = ordinaryHashImpl input :=
  probingHashQuery_eq_splitHashQuery_of_stable parameter input hstable

theorem simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hinRange : domain.InRange)
    (hchain : ∀ lay tree leafIdx chainIdx step,
      domain ≠ .chain lay tree leafIdx chainIdx step)
    (hleaf : ∀ lay tree leafIdx, domain ≠ .leaf lay tree leafIdx)
    (hnode : ∀ lay tree level nodeIdx, domain ≠ .node lay tree level nodeIdx) :
    simulateQ (probingHashImpl parameter) (tweakableHash parameter domain payload) =
      simulateQ ordinaryHashImpl (tweakableHash parameter domain payload) := by
  unfold tweakableHash oracleHash
  rw [simulateQ_bind, simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query, simulateQ_pure]
  rw [probingHashImpl_eq_ordinaryHashImpl_of_stable parameter _
    (stableOrdinaryInput_tweakableHashInput parameter domain payload hinRange
      hchain hleaf hnode)]

theorem simulateQ_probingHashImpl_messageDigest_eq_ordinaryHashImpl
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    simulateQ (probingHashImpl parameter)
        (messageDigest parameter root message randomness) =
      simulateQ ordinaryHashImpl
        (messageDigest parameter root message randomness) := by
  unfold messageDigest oracleHash
  rw [simulateQ_bind, simulateQ_bind]
  simp only [HasQuery.instOfMonadLift_query, simulateQ_spec_query, simulateQ_pure]
  rw [probingHashImpl_eq_ordinaryHashImpl_of_stable parameter _
    (stableOrdinaryInput_tweakableHashInput parameter .message _ (by trivial)
      (by simp) (by simp) (by simp))]

theorem simulateQ_probingHashImpl_ftsLeafHash_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (secret : Digest) :
    simulateQ (probingHashImpl parameter)
        (ftsLeafHash parameter index tree leafIdx secret) =
      simulateQ ordinaryHashImpl
        (ftsLeafHash parameter index tree leafIdx secret) := by
  unfold ftsLeafHash
  exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
    (.ftsLeaf index tree leafIdx) (digestBytes secret) (by trivial)
      (by simp) (by simp) (by simp)

theorem simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leafIdx : FtsLeaf) (path : Fin ftsTreeHeight → Digest) :
    ∀ levels value, levels ≤ ftsTreeHeight →
      simulateQ (probingHashImpl parameter)
          (ftsFold parameter index tree leafIdx path levels value) =
        simulateQ ordinaryHashImpl
          (ftsFold parameter index tree leafIdx path levels value)
  | 0, value, _ => by simp [ftsFold]
  | levels + 1, value, hlevels => by
      rw [ftsFold_succ_eq, simulateQ_bind, simulateQ_bind,
        simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl parameter index tree
          leafIdx path levels value (by omega)]
      apply bind_congr
      intro current
      split <;> split <;>
        exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
          (.ftsNode index tree (levels + 1) (leafIdx.val / 2 ^ (levels + 1))) _
            (by
              show levels + 1 < 2 ^ 32 ∧ leafIdx.val / 2 ^ (levels + 1) < 2 ^ 32
              constructor
              · have hheight : ftsTreeHeight < 2 ^ 32 := by
                  norm_num [ftsTreeHeight]
                omega
              · have hleaf : leafIdx.val < 2 ^ 32 := by
                  exact lt_of_lt_of_le leafIdx.isLt (by norm_num [ftsTreeHeight])
                have hdiv := Nat.div_le_self leafIdx.val (2 ^ (levels + 1))
                omega)
            (by simp) (by simp) (by simp)

theorem simulateQ_probingHashImpl_sequenceFin_eq_ordinaryHashImpl
    (parameter : PublicParameter) {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomponent : ∀ position,
      simulateQ (probingHashImpl parameter) (computation position) =
        simulateQ ordinaryHashImpl (computation position)) :
    simulateQ (probingHashImpl parameter) (sequenceFin computation) =
      simulateQ ordinaryHashImpl (sequenceFin computation) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind, simulateQ_bind, hcomponent 0]
      apply bind_congr
      intro head
      rw [simulateQ_bind, simulateQ_bind]
      have htail := ih (fun position : Fin n => computation position.succ)
        (fun position => hcomponent position.succ)
      rw [htail]
      simp only [simulateQ_pure]

theorem simulateQ_probingHashImpl_ftsRecover_eq_ordinaryHashImpl
    (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    simulateQ (probingHashImpl parameter)
        (ftsRecover parameter index leaves secrets paths) =
      simulateQ ordinaryHashImpl
        (ftsRecover parameter index leaves secrets paths) := by
  unfold ftsRecover
  rw [simulateQ_bind, simulateQ_bind]
  have hroots := simulateQ_probingHashImpl_sequenceFin_eq_ordinaryHashImpl parameter
    (fun tree => do
      let leaf := leaves (ftsIndexOf tree)
      let value ← ftsLeafHash parameter index tree leaf (secrets tree)
      ftsFold parameter index tree leaf (paths tree) ftsTreeHeight value)
    (fun tree => by
      rw [simulateQ_bind, simulateQ_bind,
        simulateQ_probingHashImpl_ftsLeafHash_eq_ordinaryHashImpl]
      apply bind_congr
      intro value
      exact simulateQ_probingHashImpl_ftsFold_eq_ordinaryHashImpl parameter index tree
        (leaves (ftsIndexOf tree)) (paths tree) ftsTreeHeight value le_rfl)
  rw [hroots]
  apply bind_congr
  intro roots
  exact simulateQ_probingHashImpl_tweakableHash_eq_ordinaryHashImpl parameter
    (.ftsRoots index) (ftsRootsPayload roots) (by trivial)
      (by simp) (by simp) (by simp)

theorem relTriple_runRaw_splitUniformImpl
    (n : Nat) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
        pure (output, ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := Fin (n + 1)) state fuel) := by
  let uniform : ProbComp (Fin (n + 1)) := liftM (unifSpec.query n)
  have hself : RelTriple uniform uniform fun left right => left = right :=
    relTriple_refl uniform
  have hpre : RelTriple uniform uniform fun left right =>
      RawOrdinaryResultRelAt state fuel
        (.done state fuel (left, cache)) (right, ordinaryQueryCache cache) := by
    apply relTriple_post_mono hself
    intro left right heq
    subst right
    simp [RawOrdinaryResultRelAt]
  have hmapped := relTriple_map
    (R := RawOrdinaryResultRelAt (alpha := Fin (n + 1)) state fuel)
    (f := fun output => LazyRevealProbe.RawResult.done state fuel (output, cache))
    (g := fun output => (output, ordinaryQueryCache cache)) hpre
  simpa [uniform, splitUniformImpl, LazyRevealProbe.uniformQuery,
    LazyRevealProbe.runRaw_uniform_query_bind, LazyRevealProbe.runRaw,
    map_eq_bind_pure_comp] using hmapped

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryHashImpl
    [Inhabited alpha]
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (RawOrdinaryResultRel (alpha := alpha)) := by
  have hproject :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_of_project_eq_some_exact
      projectRawOrdinary
      (default, ∅)
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (projectRawOrdinary_simulateQ_ordinaryHashImpl computation state cache fuel)
  apply relTriple_post_mono hproject
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => simp [projectRawOrdinary] at hrelation
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      change ordinaryResult = (value, ordinaryQueryCache finalCache)
      exact (Option.some.inj hrelation).symm

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryHashImpl_at
    [Inhabited alpha]
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := alpha) state fuel) := by
  have hbase := relTriple_runRaw_simulateQ_ordinaryHashImpl computation state cache fuel
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => match result with
        | .stopped _ => True
        | .done finalState remaining _ => finalState = state ∧ remaining = fuel)
      (by
        intro result hresult
        cases result with
        | stopped hit => trivial
        | done finalState remaining valueCache =>
            rcases valueCache with ⟨value, finalCache⟩
            have hprojection := mem_runRaw_simulateQ_ordinaryHashImpl_projects computation state
              finalState cache finalCache fuel remaining value hresult
            exact ⟨hprojection.1, hprojection.2.1⟩)
  apply relTriple_post_mono hsupported
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => exact hrelation.1
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      exact ⟨hrelation.2.1, hrelation.2.2, hrelation.1⟩

set_option maxRecDepth 10000 in
theorem relTriple_runRaw_simulateQ_ordinaryRomImpl
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    RelTriple
      (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryRomImpl computation).run cache))
      ((simulateQ romImpl computation).run (ordinaryQueryCache cache))
      (RawOrdinaryResultRelAt (alpha := alpha) state fuel) := by
  induction computation using OracleComp.inductionOn generalizing state cache fuel with
  | pure value =>
      simp [LazyRevealProbe.runRaw, RawOrdinaryResultRelAt]
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, LazyRevealProbe.runRaw_bind,
        simulateQ_query_bind, StateT.run_bind]
      have hquery : RelTriple
          (LazyRevealProbe.runRaw state fuel ((ordinaryRomImpl query).run cache))
          ((romImpl query).run (ordinaryQueryCache cache))
          (RawOrdinaryResultRelAt state fuel) := by
        cases query with
        | inl n =>
            change RelTriple
              (LazyRevealProbe.runRaw state fuel ((splitUniformImpl n).run cache))
              ((unifFwdImpl HashSpec n).run (ordinaryQueryCache cache))
              (RawOrdinaryResultRelAt state fuel)
            rw [show (unifFwdImpl HashSpec n).run (ordinaryQueryCache cache) =
                (fun output => (output, ordinaryQueryCache cache)) <$>
                  (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) by
              simpa using unifFwdImpl.simulateQ_run
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
                (ordinaryQueryCache cache)]
            simpa [map_eq_bind_pure_comp] using
              relTriple_runRaw_splitUniformImpl n state cache fuel
        | inr input =>
            simpa [ordinaryRomImpl, romImpl] using
              relTriple_runRaw_simulateQ_ordinaryHashImpl_at
                (liftM (HashSpec.query input)) state cache fuel
      apply relTriple_bind hquery
      intro rawResult ordinaryResult hrelation
      cases rawResult with
      | stopped hit => simp [RawOrdinaryResultRelAt] at hrelation
      | done finalState remaining valueCache =>
          rcases valueCache with ⟨value, finalCache⟩
          rcases hrelation with ⟨rfl, rfl, rfl⟩
          exact ih value finalState finalCache remaining

set_option maxRecDepth 10000 in
theorem evalDist_projectRawOrdinary_simulateQ_ordinaryRomImpl
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache) (fuel : Nat) :
    𝒟[projectRawOrdinary <$>
        LazyRevealProbe.runRaw state fuel
          ((simulateQ ordinaryRomImpl computation).run cache)] =
      𝒟[some <$>
        (simulateQ romImpl computation).run (ordinaryQueryCache cache)] := by
  refine evalDist_map_eq_of_relTriple (relTriple_post_mono
    (relTriple_runRaw_simulateQ_ordinaryRomImpl computation state cache fuel) ?_)
  intro rawResult ordinaryResult hrelation
  cases rawResult with
  | stopped hit => simp [RawOrdinaryResultRelAt] at hrelation
  | done finalState remaining valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      rcases hrelation with ⟨_, _, rfl⟩
      rfl

set_option maxRecDepth 10000 in
theorem mem_runRaw_simulateQ_ordinaryRomImpl_projects
    [Inhabited alpha]
    (computation : OracleComp OracleWorld alpha)
    (state finalState : LazyRevealProbe.State Coordinate)
    (cache finalCache : SplitHashCache) (fuel remaining : Nat) (value : alpha)
    (hresult : LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
      support (LazyRevealProbe.runRaw state fuel
        ((simulateQ ordinaryRomImpl computation).run cache))) :
    finalState = state ∧ remaining = fuel ∧
      (value, ordinaryQueryCache finalCache) ∈ support
        ((simulateQ romImpl computation).run (ordinaryQueryCache cache)) := by
  obtain ⟨ordinaryResult, hordinary, hrelation⟩ :=
    exists_right_mem_support_of_relTriple
      (relTriple_runRaw_simulateQ_ordinaryRomImpl computation state cache fuel) hresult
  exact ⟨hrelation.1, hrelation.2.1, hrelation.2.2 ▸ hordinary⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
