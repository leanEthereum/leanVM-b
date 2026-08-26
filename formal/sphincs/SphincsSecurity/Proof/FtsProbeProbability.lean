import SphincsSecurity.Proof.FtsProbeTerminal
import VCVio.ProgramLogic.Relational.Basic

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem tableHits_addPending_eq_true_of_true
    (state : AdaptiveRevealProbe.State Coordinate) (table : Coordinate → Digest)
    (coordinate : Coordinate) (candidate : Digest)
    (hhit : AdaptiveRevealProbe.tableHits state table = true) :
    AdaptiveRevealProbe.tableHits (state.addPending coordinate candidate) table = true := by
  classical
  rw [AdaptiveRevealProbe.tableHits, decide_eq_true_eq] at hhit ⊢
  obtain ⟨other, hmem⟩ := hhit
  refine ⟨other, ?_⟩
  by_cases heq : other = coordinate
  · subst other
    simp [AdaptiveRevealProbe.State.addPending, hmem]
  · simpa [AdaptiveRevealProbe.State.addPending, Function.update_of_ne heq] using hmem

theorem tableHits_install_eq_true_of_true
    (state : AdaptiveRevealProbe.State Coordinate) (table : Coordinate → Digest)
    (coordinate : Coordinate) (value : Digest)
    (hhit : AdaptiveRevealProbe.tableHits state table = true)
    (hmiss : table coordinate ∉ state.pending coordinate) :
    AdaptiveRevealProbe.tableHits (state.install coordinate value) table = true := by
  classical
  rw [AdaptiveRevealProbe.tableHits, decide_eq_true_eq] at hhit ⊢
  obtain ⟨other, hmem⟩ := hhit
  have hne : other ≠ coordinate := by
    intro heq
    subst other
    exact hmiss hmem
  exact ⟨other, by
    simpa [AdaptiveRevealProbe.State.install, Function.update_of_ne hne] using hmem⟩

theorem runDetailed_hit_eq_true_of_tableHits_eq_true
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate)
    (fuel : Nat) (computation : OracleComp (AdaptiveRevealProbe.World Coordinate) alpha)
    (hhit : AdaptiveRevealProbe.tableHits state table = true) :
    ∀ result ∈ support (AdaptiveRevealProbe.runDetailed table state fuel computation),
      result.hit = true := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      intro detailed hdetailed
      simp [AdaptiveRevealProbe.runDetailed, hhit] at hdetailed
      subst detailed
      rfl
  | query_bind input next ih =>
      intro result hresult
      cases input with
      | uniform n =>
          rw [AdaptiveRevealProbe.runDetailed_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hhit result hrest
      | hashOutput =>
          rw [AdaptiveRevealProbe.runDetailed_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hhit result hrest
      | probe coordinate candidate =>
          rw [AdaptiveRevealProbe.runDetailed_probe_query_bind] at hresult
          cases fuel with
          | zero =>
              simp [hhit] at hresult
              subst result
              rfl
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | none =>
                  exact ih () (state.addPending coordinate candidate) remaining
                    (tableHits_addPending_eq_true_of_true state table coordinate candidate hhit)
                    result (by simpa [hrevealed] using hresult)
              | some value =>
                  exact ih () state remaining hhit result (by simpa [hrevealed] using hresult)
      | reveal coordinate =>
          rw [AdaptiveRevealProbe.runDetailed_reveal_query_bind] at hresult
          cases hrevealed : state.revealed coordinate with
          | some value =>
              exact ih value state fuel hhit result (by simpa [hrevealed] using hresult)
          | none =>
              by_cases hcandidate : table coordinate ∈ state.pending coordinate
              · simp [hrevealed, hcandidate] at hresult
                subst result
                rfl
              · exact ih (table coordinate) (state.install coordinate (table coordinate)) fuel
                  (tableHits_install_eq_true_of_true state table coordinate
                    (table coordinate) hhit hcandidate)
                  result (by simpa [hrevealed, hcandidate] using hresult)

theorem relTriple_and_left_support
    {left : ProbComp alpha} {right : ProbComp beta}
    {relation : alpha → beta → Prop} (hrel : RelTriple left right relation)
    (property : alpha → Prop) (hproperty : ∀ result ∈ support left, property result) :
    RelTriple left right fun leftResult rightResult =>
      relation leftResult rightResult ∧ property leftResult := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel ⊢
  obtain ⟨coupling, hrelation⟩ := hrel
  refine ⟨coupling, fun result hresult => ⟨hrelation result hresult, ?_⟩⟩
  apply hproperty result.1
  rw [mem_support_iff_evalDist_apply_ne_zero]
  rw [← SPMF.mem_support_iff]
  have hmap : result.1 ∈ support
      (Prod.fst <$> coupling.1 : SPMF alpha) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  rwa [coupling.2.map_fst] at hmap

theorem relTriple_of_project_eq_some
    (project : alpha → Option beta) (fallback : beta)
    (left : ProbComp alpha) (right : ProbComp beta)
    (heq : project <$> left = some <$> right) :
    RelTriple left right fun leftResult rightResult =>
      project leftResult = none ∨ project leftResult = some rightResult := by
  let recover : alpha → beta := fun result => (project result).getD fallback
  have hrecover : recover <$> left = right := by
    calc
      recover <$> left = (fun result : Option beta => result.getD fallback) <$>
          (project <$> left) := by
        simp [recover, Functor.map_map]
      _ = (fun result : Option beta => result.getD fallback) <$> (some <$> right) := by
        rw [heq]
      _ = right := by simp
  have hself : RelTriple left left fun leftResult rightResult =>
      project leftResult = none ∨
        project leftResult = some (recover rightResult) := by
    apply relTriple_post_mono (relTriple_refl left)
    intro leftResult rightResult heqResult
    subst rightResult
    cases hproject : project leftResult with
    | none => exact Or.inl rfl
    | some result =>
        exact Or.inr (by simp [recover, hproject])
  have hmapped := relTriple_map
    (R := fun leftResult rightResult =>
      project leftResult = none ∨ project leftResult = some rightResult)
    (f := id) (g := recover) hself
  simpa [hrecover] using hmapped

theorem relTriple_of_project_eq_some_exact
    (project : alpha → Option beta) (fallback : beta)
    (left : ProbComp alpha) (right : ProbComp beta)
    (heq : project <$> left = some <$> right) :
    RelTriple left right fun leftResult rightResult =>
      project leftResult = some rightResult := by
  have hweak := relTriple_of_project_eq_some project fallback left right heq
  have hpresent : ∀ result ∈ support left, project result ≠ none := by
    intro result hresult hnone
    have hleftNone : none ∈ support (project <$> left) := by
      rw [support_map]
      exact ⟨result, hresult, hnone⟩
    rw [heq, support_map] at hleftNone
    obtain ⟨rightResult, _hright, hsome⟩ := hleftNone
    simp at hsome
  apply relTriple_post_mono
    (relTriple_and_left_support hweak (fun result => project result ≠ none) hpresent)
  intro leftResult rightResult hresult
  rcases hresult.1 with hnone | hsome
  · exact (hresult.2 hnone).elim
  · exact hsome

theorem relTriple_of_coupledAt [Inhabited alpha]
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {masked : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {ordinary : StateT (QueryCache HashSpec) ProbComp alpha}
    {cache : SplitHashCache}
    (hcoupled : CoupledAt parameter table state fuel masked ordinary cache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache))
      (ordinary.run (mergedCache parameter table cache))
      fun maskedResult ordinaryResult =>
        projectDetailedCache parameter table maskedResult = some ordinaryResult := by
  exact relTriple_of_project_eq_some_exact
    (projectDetailedCache parameter table)
    (default, ∅)
    (AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache))
    (ordinary.run (mergedCache parameter table cache)) hcoupled

def CleanResultRel (parameter : PublicParameter) (table : Coordinate → Digest) :
    AdaptiveRevealProbe.DetailedResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop
  | .stopped _, _ => False
  | .done hit finalState (value, finalCache), ordinaryResult =>
      hit = false ∧
        ordinaryResult = (value, mergedCache parameter table finalCache) ∧
          AdaptiveRevealProbe.tableHits finalState table = false ∧
          RevealedSynced parameter table finalState finalCache

def CleanStepRel (parameter : PublicParameter) (table : Coordinate → Digest) :
    AdaptiveRevealProbe.DetailedResult Coordinate (alpha × SplitHashCache) →
      (alpha × QueryCache HashSpec) → Prop :=
  fun maskedResult ordinaryResult => maskedResult.hit = true ∨
    CleanResultRel parameter table maskedResult ordinaryResult

theorem relTriple_of_coupledAt_cleanOnly [Inhabited alpha]
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {masked : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {ordinary : StateT (QueryCache HashSpec) ProbComp alpha}
    {cache : SplitHashCache}
    (hcoupled : CoupledAt parameter table state fuel masked ordinary cache)
    (hinvariants : ∀ finalState value finalCache,
      .done false finalState (value, finalCache) ∈ support
          (AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache)) →
        AdaptiveRevealProbe.tableHits finalState table = false ∧
          RevealedSynced parameter table finalState finalCache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache))
      (ordinary.run (mergedCache parameter table cache))
      (CleanResultRel parameter table) := by
  let left := AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache)
  let right := ordinary.run (mergedCache parameter table cache)
  have hproject : RelTriple left right fun maskedResult ordinaryResult =>
      projectDetailedCache parameter table maskedResult = some ordinaryResult :=
    relTriple_of_coupledAt hcoupled
  have hsupported : ∀ result ∈ support left,
      ∀ finalState value finalCache,
        result = .done false finalState (value, finalCache) →
          AdaptiveRevealProbe.tableHits finalState table = false ∧
            RevealedSynced parameter table finalState finalCache := by
    intro result hresult finalState value finalCache hresultEq
    subst result
    exact hinvariants finalState value finalCache hresult
  apply relTriple_post_mono
    (relTriple_and_left_support hproject
      (fun result => ∀ finalState value finalCache,
        result = .done false finalState (value, finalCache) →
          AdaptiveRevealProbe.tableHits finalState table = false ∧
            RevealedSynced parameter table finalState finalCache)
      hsupported)
  intro maskedResult ordinaryResult hresult
  cases maskedResult with
  | stopped hit => simp [projectDetailedCache] at hresult
  | done hit finalState valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      cases hit with
      | false =>
          have heq : ordinaryResult =
              (value, mergedCache parameter table finalCache) := by
            simpa [projectDetailedCache] using hresult.1.symm
          exact ⟨rfl, heq, hresult.2 finalState value finalCache rfl⟩
      | true => simp [projectDetailedCache] at hresult

theorem relTriple_of_coupledAt_clean [Inhabited alpha]
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {masked : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {ordinary : StateT (QueryCache HashSpec) ProbComp alpha}
    {cache : SplitHashCache}
    (hcoupled : CoupledAt parameter table state fuel masked ordinary cache)
    (hinvariants : ∀ finalState value finalCache,
      .done false finalState (value, finalCache) ∈ support
          (AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache)) →
        AdaptiveRevealProbe.tableHits finalState table = false ∧
          RevealedSynced parameter table finalState finalCache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache))
      (ordinary.run (mergedCache parameter table cache))
      (CleanStepRel parameter table) := by
  apply relTriple_post_mono
    (relTriple_of_coupledAt_cleanOnly hcoupled hinvariants)
  intro maskedResult ordinaryResult hresult
  exact Or.inr hresult

theorem relTriple_of_coupledAt_stateFree [Inhabited alpha]
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state : AdaptiveRevealProbe.State Coordinate} {fuel : Nat}
    {masked : StateT SplitHashCache
      (OracleComp (AdaptiveRevealProbe.World Coordinate)) alpha}
    {ordinary : StateT (QueryCache HashSpec) ProbComp alpha}
    {cache : SplitHashCache}
    (hcoupled : CoupledAt parameter table state fuel masked ordinary cache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hstateFree : StateFree masked) (hcache : CachePreserving masked) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state fuel (masked.run cache))
      (ordinary.run (mergedCache parameter table cache))
      (CleanResultRel parameter table) := by
  apply relTriple_of_coupledAt_cleanOnly hcoupled
  intro finalState value finalCache hresult
  obtain ⟨resultValue, heq⟩ := AdaptiveRevealProbe.runDetailed_stateFree_support table state
    fuel (masked.run cache) (hstateFree cache) hclean
    (.done false finalState (value, finalCache)) hresult
  have hstate : finalState = state :=
    (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1
  exact ⟨hstate ▸ hclean,
    revealedSynced_of_mem_runDetailed_stateFree parameter table state finalState fuel cache
      finalCache value masked hclean hsynced hstateFree hcache hresult⟩

theorem relTriple_runDetailed_of_tableHits_eq_true
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (left : OracleComp (AdaptiveRevealProbe.World Coordinate)
      (alpha × SplitHashCache))
    (right : ProbComp (alpha × QueryCache HashSpec))
    (hhit : AdaptiveRevealProbe.tableHits state table = true) :
    RelTriple (AdaptiveRevealProbe.runDetailed table state fuel left) right
      (CleanStepRel parameter table) := by
  apply relTriple_post_mono
    (relTriple_and_left_support
      (relTriple_true (AdaptiveRevealProbe.runDetailed table state fuel left) right)
      (fun result => result.hit = true)
      (runDetailed_hit_eq_true_of_tableHits_eq_true table state fuel left hhit))
  intro leftResult rightResult hresult
  exact Or.inl hresult.2

theorem relTriple_runDetailed_bind_cleanOnly
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (left : OracleComp (AdaptiveRevealProbe.World Coordinate)
      (alpha × SplitHashCache))
    (next : (alpha × SplitHashCache) →
      OracleComp (AdaptiveRevealProbe.World Coordinate) (beta × SplitHashCache))
    (ordinaryLeft : ProbComp (alpha × QueryCache HashSpec))
    (ordinaryNext : (alpha × QueryCache HashSpec) →
      ProbComp (beta × QueryCache HashSpec))
    (hprobeFree : left.IsQueryBoundP AdaptiveRevealProbe.IsProbe 0)
    (hleft : RelTriple
      (AdaptiveRevealProbe.runDetailed table state fuel left) ordinaryLeft
      (CleanResultRel parameter table))
    (hnext : ∀ finalState value finalCache,
      AdaptiveRevealProbe.tableHits finalState table = false →
      RevealedSynced parameter table finalState finalCache →
      RelTriple
        (AdaptiveRevealProbe.runDetailed table finalState fuel
          (next (value, finalCache)))
        (ordinaryNext (value, mergedCache parameter table finalCache))
        (CleanStepRel parameter table)) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state fuel (left >>= next))
      (ordinaryLeft >>= ordinaryNext)
      (CleanStepRel parameter table) := by
  rw [AdaptiveRevealProbe.runDetailed_bind_probeFree table state fuel left next hprobeFree]
  apply relTriple_bind hleft
  intro leftResult rightResult hresult
  cases leftResult with
  | stopped hit => simp [CleanResultRel] at hresult
  | done hit finalState valueCache =>
      rcases valueCache with ⟨value, finalCache⟩
      simp only [CleanResultRel] at hresult
      obtain ⟨rfl, rfl, hclean, hsynced⟩ := hresult
      exact hnext finalState value finalCache hclean hsynced

set_option maxRecDepth 10000 in
theorem relTriple_maskedExpandedAdversaryImpl_step
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (cache : SplitHashCache) (input : (OracleWorld + SigningSpec).Domain)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((maskedExpandedAdversaryImpl secretKey.parameter secretKey input).run cache))
      ((unloggedMappedAdversaryImpl
        (secretKeyWithFtsTable secretKey table) input).run
          (mergedCache secretKey.parameter table cache))
      (CleanStepRel secretKey.parameter table) := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl n =>
          change RelTriple
            (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
              ((splitUniformImpl n).run cache))
            ((unifFwdImpl HashSpec n).run
              (mergedCache secretKey.parameter table cache)) _
          apply relTriple_of_coupledAt_clean
            ((coupled_splitUniformImpl secretKey.parameter table state
              (remaining + 1) n hclean).coupledAt cache)
          intro finalState output finalCache hresult
          exact ⟨tableHits_false_of_mem_runDetailed_probeFree table state finalState
              (remaining + 1) ((splitUniformImpl n).run cache)
              (splitUniformImpl_probeFree n cache) hclean (output, finalCache) hresult,
            revealedSynced_of_mem_runDetailed_stateFree secretKey.parameter table state
              finalState (remaining + 1) cache finalCache output (splitUniformImpl n)
              hclean hsynced (splitUniformImpl_stateFree n)
              (splitUniformImpl_cachePreserving n) hresult⟩
      | inr hashInput =>
          change RelTriple
            (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
              ((probingHashQuery secretKey.parameter hashInput).run cache))
            ((randomOracle hashInput).run
              (mergedCache secretKey.parameter table cache)) _
          cases hdecode : decodeProbe? secretKey.parameter hashInput with
          | none =>
              apply relTriple_of_coupledAt_clean
                (runDetailed_probingHashQuery_decode_none secretKey.parameter table state
                  (remaining + 1) cache hashInput hdecode hclean)
              intro finalState output finalCache hresult
              exact ⟨probingHashQuery_done_false_clean secretKey.parameter table state
                  finalState (remaining + 1) cache finalCache hashInput output hclean hresult,
                probingHashQuery_done_false_revealedSynced secretKey.parameter table state
                  finalState (remaining + 1) cache finalCache hashInput output hclean hsynced
                  hresult⟩
          | some probe =>
              cases hrevealed : state.revealed
                  (probe.index, probe.tree, probe.leafIdx) with
              | none =>
                  by_cases hhit : table (probe.index, probe.tree, probe.leafIdx) =
                      probe.candidate
                  · have hleft : ∀ result ∈ support
                        (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                          ((probingHashQuery secretKey.parameter hashInput).run cache)),
                        result.hit = true := by
                      intro result hresult
                      exact runDetailed_probingHashQuery_hidden_hit secretKey.parameter table
                        state remaining cache hashInput probe hdecode hrevealed hhit result hresult
                    apply relTriple_post_mono
                      (relTriple_and_left_support
                        (relTriple_true
                          (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                            ((probingHashQuery secretKey.parameter hashInput).run cache))
                          ((randomOracle hashInput).run
                            (mergedCache secretKey.parameter table cache)))
                        (fun result => result.hit = true) hleft)
                    intro maskedResult ordinaryResult hresult
                    cases maskedResult with
                    | stopped hit =>
                        left
                        simpa [AdaptiveRevealProbe.DetailedResult.hit] using hresult.2
                    | done hit finalState valueCache =>
                        left
                        simpa [AdaptiveRevealProbe.DetailedResult.hit] using hresult.2
                  · apply relTriple_of_coupledAt_clean
                      (runDetailed_probingHashQuery_hidden_miss secretKey.parameter table state
                        remaining cache hashInput probe hdecode hrevealed hclean hhit)
                    intro finalState output finalCache hresult
                    exact ⟨probingHashQuery_done_false_clean secretKey.parameter table state
                        finalState (remaining + 1) cache finalCache hashInput output hclean hresult,
                      probingHashQuery_done_false_revealedSynced secretKey.parameter table state
                        finalState (remaining + 1) cache finalCache hashInput output hclean hsynced
                        hresult⟩
              | some revealedValue =>
                  by_cases hhit : table (probe.index, probe.tree, probe.leafIdx) =
                      probe.candidate
                  · apply relTriple_of_coupledAt_clean
                      (runDetailed_probingHashQuery_revealed_hit secretKey.parameter table state
                        remaining cache hashInput probe hdecode revealedValue hrevealed hclean
                        hhit hsynced)
                    intro finalState output finalCache hresult
                    exact ⟨probingHashQuery_done_false_clean secretKey.parameter table state
                        finalState (remaining + 1) cache finalCache hashInput output hclean hresult,
                      probingHashQuery_done_false_revealedSynced secretKey.parameter table state
                        finalState (remaining + 1) cache finalCache hashInput output hclean hsynced
                        hresult⟩
                  · apply relTriple_of_coupledAt_clean
                      (runDetailed_probingHashQuery_revealed_miss secretKey.parameter table state
                        remaining cache hashInput probe hdecode revealedValue hrevealed hclean
                        hhit)
                    intro finalState output finalCache hresult
                    exact ⟨probingHashQuery_done_false_clean secretKey.parameter table state
                        finalState (remaining + 1) cache finalCache hashInput output hclean hresult,
                      probingHashQuery_done_false_revealedSynced secretKey.parameter table state
                        finalState (remaining + 1) cache finalCache hashInput output hclean hsynced
                        hresult⟩
  | inr message =>
      change RelTriple
        (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
          ((maskedSigningImpl secretKey message).run cache))
        ((simulateQ romImpl
          (scheme.sign (secretKeyWithFtsTable secretKey table) message)).run
            (mergedCache secretKey.parameter table cache)) _
      apply relTriple_of_coupledAt_clean
        (coupledAt_maskedSigningImpl secretKey table state (remaining + 1) cache message
          hclean hsynced)
      intro finalState output finalCache hresult
      exact ⟨tableHits_false_of_mem_runDetailed_probeFree table state finalState
          (remaining + 1) ((maskedSigningImpl secretKey message).run cache)
          (by
            have hprobeFree : ProbeFree (maskedSigningImpl secretKey message) := by
              unfold maskedSigningImpl
              exact (maskedSignWithView_probeFree secretKey message).map Prod.fst
            exact hprobeFree cache)
          hclean (output, finalCache) hresult,
        revealedSynced_of_mem_runDetailed_maskedSigningImpl secretKey table state finalState
          (remaining + 1) cache finalCache message hclean hsynced output hresult⟩

set_option maxRecDepth 30000 in
theorem relTriple_simulateQ_maskedExpandedAdversaryImpl
    (secretKey : SecretKey) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (state : AdaptiveRevealProbe.State Coordinate) (fuel : Nat)
    (cache : SplitHashCache)
    (hbound : computation.IsQueryBoundP isDirectHashQuery fuel)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced secretKey.parameter table state cache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state fuel
        ((simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
          computation).run cache))
      ((simulateQ
        (unloggedMappedAdversaryImpl (secretKeyWithFtsTable secretKey table))
        computation).run (mergedCache secretKey.parameter table cache))
      (CleanStepRel secretKey.parameter table) := by
  induction computation using OracleComp.inductionOn generalizing state fuel cache with
  | pure result =>
      simp [simulateQ_pure, AdaptiveRevealProbe.runDetailed, hclean,
        CleanStepRel, CleanResultRel, hsynced]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | inl worldInput =>
          cases worldInput with
          | inl n =>
              rw [simulateQ_query_bind, simulateQ_query_bind,
                StateT.run_bind, StateT.run_bind]
              change RelTriple
                (AdaptiveRevealProbe.runDetailed table state fuel
                  ((splitUniformImpl n).run cache >>= fun result =>
                    (simulateQ
                      (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                      (next result.1)).run result.2))
                ((unifFwdImpl HashSpec n).run
                    (mergedCache secretKey.parameter table cache) >>= fun result =>
                  (simulateQ
                    (unloggedMappedAdversaryImpl
                      (secretKeyWithFtsTable secretKey table))
                    (next result.1)).run result.2) _
              apply relTriple_runDetailed_bind_cleanOnly secretKey.parameter table state fuel
                ((splitUniformImpl n).run cache)
                (fun result =>
                  (simulateQ
                    (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                    (next result.1)).run result.2)
                ((unifFwdImpl HashSpec n).run
                  (mergedCache secretKey.parameter table cache))
                (fun result =>
                  (simulateQ
                    (unloggedMappedAdversaryImpl
                      (secretKeyWithFtsTable secretKey table))
                    (next result.1)).run result.2)
                (splitUniformImpl_probeFree n cache)
              · exact relTriple_of_coupledAt_stateFree
                  ((coupled_splitUniformImpl secretKey.parameter table state fuel n hclean).coupledAt
                    cache) hclean hsynced (splitUniformImpl_stateFree n)
                  (splitUniformImpl_cachePreserving n)
              · intro finalState output finalCache hfinalClean hfinalSynced
                exact ih output finalState fuel finalCache
                  (by simpa [isDirectHashQuery] using hbound.2 output)
                  hfinalClean hfinalSynced
          | inr hashInput =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) alpha at next
              have hpositive : 0 < fuel := by
                simpa [isDirectHashQuery] using hbound.1
              cases fuel with
              | zero => omega
              | succ remaining =>
                  rw [simulateQ_query_bind, simulateQ_query_bind,
                    StateT.run_bind, StateT.run_bind]
                  change RelTriple
                    (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                      ((probingHashQuery secretKey.parameter hashInput).run cache >>= fun result =>
                        (simulateQ
                          (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                          (next result.1)).run result.2))
                    ((randomOracle hashInput).run
                        (mergedCache secretKey.parameter table cache) >>= fun result =>
                      (simulateQ
                        (unloggedMappedAdversaryImpl
                          (secretKeyWithFtsTable secretKey table))
                        (next result.1)).run result.2) _
                  cases hdecode : decodeProbe? secretKey.parameter hashInput with
                  | none =>
                      have hstateFree : StateFree
                          (probingHashQuery secretKey.parameter hashInput) := by
                        intro workingCache
                        rw [probingHashQuery_run_eq, hdecode]
                        exact splitHashQuery_stateFree (.ordinary hashInput) workingCache
                      have hprobeFree : ProbeFree
                          (probingHashQuery secretKey.parameter hashInput) := by
                        intro workingCache
                        rw [probingHashQuery_run_eq, hdecode]
                        exact splitHashQuery_probeFree (.ordinary hashInput) workingCache
                      apply relTriple_runDetailed_bind_cleanOnly secretKey.parameter table state
                        (remaining + 1)
                        ((probingHashQuery secretKey.parameter hashInput).run cache)
                        (fun result =>
                          (simulateQ
                            (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                            (next result.1)).run result.2)
                        ((randomOracle hashInput).run
                          (mergedCache secretKey.parameter table cache))
                        (fun result =>
                          (simulateQ
                            (unloggedMappedAdversaryImpl
                              (secretKeyWithFtsTable secretKey table))
                            (next result.1)).run result.2)
                        (hprobeFree cache)
                      · exact relTriple_of_coupledAt_stateFree
                          (runDetailed_probingHashQuery_decode_none secretKey.parameter table state
                            (remaining + 1) cache hashInput hdecode hclean)
                          hclean hsynced hstateFree
                          (probingHashQuery_cachePreserving secretKey.parameter hashInput)
                      · intro finalState output finalCache hfinalClean hfinalSynced
                        have htail : (next output).IsQueryBoundP
                            isDirectHashQuery remaining := by
                          simpa [isDirectHashQuery] using hbound.2 output
                        exact ih output finalState (remaining + 1) finalCache
                          (htail.mono (Nat.le_succ remaining)) hfinalClean hfinalSynced
                  | some probe =>
                      rw [probingHashQuery_run_eq, hdecode]
                      change RelTriple
                        (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                          ((AdaptiveRevealProbe.probeQuery
                              (probe.index, probe.tree, probe.leafIdx) probe.candidate >>= fun _ =>
                            (splitHashQuery (.ordinary hashInput)).run cache >>= fun result =>
                              (simulateQ
                                (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                                (next result.1)).run result.2))) _ _
                      rw [AdaptiveRevealProbe.probeQuery,
                        AdaptiveRevealProbe.runDetailed_probe_query_bind]
                      cases hrevealed : state.revealed
                          (probe.index, probe.tree, probe.leafIdx) with
                      | none =>
                          by_cases hhit : table (probe.index, probe.tree, probe.leafIdx) =
                              probe.candidate
                          · apply relTriple_runDetailed_of_tableHits_eq_true
                              secretKey.parameter table
                              (state.addPending
                                (probe.index, probe.tree, probe.leafIdx) probe.candidate)
                              remaining
                            exact AdaptiveRevealProbe.tableHits_addPending_eq_true state table
                              (probe.index, probe.tree, probe.leafIdx) probe.candidate hhit
                          · have hnextClean := AdaptiveRevealProbe.tableHits_addPending_eq_false
                              state table (probe.index, probe.tree, probe.leafIdx)
                              probe.candidate hclean hhit
                            have hordinary : IsOrdinaryInput secretKey.parameter table hashInput :=
                              isOrdinaryInput_of_decode_miss secretKey.parameter table hashInput
                                probe hdecode (fun heq => hhit heq.symm)
                            apply relTriple_runDetailed_bind_cleanOnly secretKey.parameter table
                              (state.addPending
                                (probe.index, probe.tree, probe.leafIdx) probe.candidate)
                              remaining ((splitHashQuery (.ordinary hashInput)).run cache)
                              (fun result =>
                                (simulateQ
                                  (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                                  (next result.1)).run result.2)
                              ((randomOracle hashInput).run
                                (mergedCache secretKey.parameter table cache))
                              (fun result =>
                                (simulateQ
                                  (unloggedMappedAdversaryImpl
                                    (secretKeyWithFtsTable secretKey table))
                                  (next result.1)).run result.2)
                              (splitHashQuery_probeFree (.ordinary hashInput) cache)
                            · exact relTriple_of_coupledAt_stateFree
                                (runDetailed_splitHashQuery_ordinary secretKey.parameter table
                                  (state.addPending
                                    (probe.index, probe.tree, probe.leafIdx) probe.candidate)
                                  remaining cache hashInput hnextClean hordinary)
                                hnextClean
                                (by
                                  intro coordinate value hvalue
                                  exact hsynced coordinate value (by
                                    simpa [AdaptiveRevealProbe.State.addPending] using hvalue))
                                (splitHashQuery_stateFree (.ordinary hashInput))
                                (splitHashQuery_cachePreserving (.ordinary hashInput))
                            · intro finalState output finalCache hfinalClean hfinalSynced
                              exact ih output finalState remaining finalCache
                                (by simpa [isDirectHashQuery] using hbound.2 output)
                                hfinalClean hfinalSynced
                      | some revealedValue =>
                          have htailBound : ∀ output,
                              (next output).IsQueryBoundP isDirectHashQuery remaining := by
                            intro output
                            simpa [isDirectHashQuery] using hbound.2 output
                          by_cases hhit : table (probe.index, probe.tree, probe.leafIdx) =
                              probe.candidate
                          · have hcoupled := runDetailed_probingHashQuery_revealed_hit
                              secretKey.parameter table state remaining cache hashInput probe
                              hdecode revealedValue hrevealed hclean hhit hsynced
                            rw [probingHashQuery_run_eq, hdecode] at hcoupled
                            change projectDetailedCache secretKey.parameter table <$>
                                AdaptiveRevealProbe.runDetailed table state (remaining + 1)
                                  ((AdaptiveRevealProbe.probeQuery
                                    (probe.index, probe.tree, probe.leafIdx) probe.candidate >>= fun _ =>
                                    (splitHashQuery (.ordinary hashInput)).run cache)) = _ at hcoupled
                            rw [AdaptiveRevealProbe.probeQuery,
                              AdaptiveRevealProbe.runDetailed_probe_query_bind, hrevealed]
                              at hcoupled
                            apply relTriple_runDetailed_bind_cleanOnly secretKey.parameter table
                              state remaining ((splitHashQuery (.ordinary hashInput)).run cache)
                              (fun result =>
                                (simulateQ
                                  (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                                  (next result.1)).run result.2)
                              ((randomOracle hashInput).run
                                (mergedCache secretKey.parameter table cache))
                              (fun result =>
                                (simulateQ
                                  (unloggedMappedAdversaryImpl
                                    (secretKeyWithFtsTable secretKey table))
                                  (next result.1)).run result.2)
                              (splitHashQuery_probeFree (.ordinary hashInput) cache)
                            · exact relTriple_of_coupledAt_cleanOnly hcoupled fun
                                finalState output finalCache hresult =>
                                ⟨tableHits_false_of_mem_runDetailed_probeFree table state
                                    finalState remaining
                                    ((splitHashQuery (.ordinary hashInput)).run cache)
                                    (splitHashQuery_probeFree (.ordinary hashInput) cache)
                                    hclean (output, finalCache) hresult,
                                  probingHashQuery_done_false_revealedSynced
                                    secretKey.parameter table state finalState (remaining + 1)
                                    cache finalCache hashInput output hclean hsynced (by
                                      rw [probingHashQuery_run_eq, hdecode]
                                      change .done false finalState (output, finalCache) ∈ support
                                        (AdaptiveRevealProbe.runDetailed table state
                                          (remaining + 1)
                                          (AdaptiveRevealProbe.probeQuery
                                            (probe.index, probe.tree, probe.leafIdx)
                                            probe.candidate >>= fun _ =>
                                            (splitHashQuery (.ordinary hashInput)).run cache))
                                      rw [AdaptiveRevealProbe.probeQuery,
                                        AdaptiveRevealProbe.runDetailed_probe_query_bind,
                                        hrevealed]
                                      exact hresult)⟩
                            · intro finalState output finalCache hfinalClean hfinalSynced
                              exact ih output finalState remaining finalCache
                                (htailBound output) hfinalClean hfinalSynced
                          · have hordinary : IsOrdinaryInput secretKey.parameter table hashInput :=
                              isOrdinaryInput_of_decode_miss secretKey.parameter table hashInput
                                probe hdecode (fun heq => hhit heq.symm)
                            apply relTriple_runDetailed_bind_cleanOnly secretKey.parameter table
                              state remaining ((splitHashQuery (.ordinary hashInput)).run cache)
                              (fun result =>
                                (simulateQ
                                  (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                                  (next result.1)).run result.2)
                              ((randomOracle hashInput).run
                                (mergedCache secretKey.parameter table cache))
                              (fun result =>
                                (simulateQ
                                  (unloggedMappedAdversaryImpl
                                    (secretKeyWithFtsTable secretKey table))
                                  (next result.1)).run result.2)
                              (splitHashQuery_probeFree (.ordinary hashInput) cache)
                            · exact relTriple_of_coupledAt_stateFree
                                (runDetailed_splitHashQuery_ordinary secretKey.parameter table state
                                  remaining cache hashInput hclean hordinary)
                                hclean hsynced (splitHashQuery_stateFree (.ordinary hashInput))
                                (splitHashQuery_cachePreserving (.ordinary hashInput))
                            · intro finalState output finalCache hfinalClean hfinalSynced
                              exact ih output finalState remaining finalCache
                                (htailBound output) hfinalClean hfinalSynced
      | inr message =>
          rw [simulateQ_query_bind, simulateQ_query_bind,
            StateT.run_bind, StateT.run_bind]
          change RelTriple
            (AdaptiveRevealProbe.runDetailed table state fuel
              ((maskedSigningImpl secretKey message).run cache >>= fun result =>
                (simulateQ
                  (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                  (next result.1)).run result.2))
            ((simulateQ romImpl
                (scheme.sign (secretKeyWithFtsTable secretKey table) message)).run
                  (mergedCache secretKey.parameter table cache) >>= fun result =>
              (simulateQ
                (unloggedMappedAdversaryImpl (secretKeyWithFtsTable secretKey table))
                (next result.1)).run result.2) _
          have hprobeFree : ProbeFree (maskedSigningImpl secretKey message) := by
            unfold maskedSigningImpl
            exact (maskedSignWithView_probeFree secretKey message).map Prod.fst
          apply relTriple_runDetailed_bind_cleanOnly secretKey.parameter table state fuel
            ((maskedSigningImpl secretKey message).run cache)
            (fun result =>
              (simulateQ (maskedExpandedAdversaryImpl secretKey.parameter secretKey)
                (next result.1)).run result.2)
            ((simulateQ romImpl
              (scheme.sign (secretKeyWithFtsTable secretKey table) message)).run
                (mergedCache secretKey.parameter table cache))
            (fun result =>
              (simulateQ
                (unloggedMappedAdversaryImpl (secretKeyWithFtsTable secretKey table))
                (next result.1)).run result.2)
            (hprobeFree cache)
          · exact relTriple_of_coupledAt_cleanOnly
              (coupledAt_maskedSigningImpl secretKey table state fuel cache message hclean hsynced)
              fun finalState output finalCache hresult =>
                ⟨tableHits_false_of_mem_runDetailed_probeFree table state finalState fuel
                    ((maskedSigningImpl secretKey message).run cache) (hprobeFree cache)
                    hclean (output, finalCache) hresult,
                  revealedSynced_of_mem_runDetailed_maskedSigningImpl secretKey table state
                    finalState fuel cache finalCache message hclean hsynced output hresult⟩
          · intro finalState output finalCache hfinalClean hfinalSynced
            exact ih output finalState fuel finalCache
              (by simpa [isDirectHashQuery] using hbound.2 output)
              hfinalClean hfinalSynced

theorem probEvent_right_le_projected_or_missing
    (project : alpha → Option beta) (left : ProbComp alpha) (right : ProbComp beta)
    (hrel : RelTriple left right fun leftResult rightResult =>
      project leftResult = none ∨ project leftResult = some rightResult)
    (event : beta → Prop) :
    Pr[event | right] ≤
      Pr[fun result => project result = none ∨
        ∃ value, project result = some value ∧ event value | left] := by
  apply probEvent_le_of_relTriple (relTriple_symm hrel)
  intro rightResult leftResult hrelation hevent
  rcases hrelation with hmissing | hpresent
  · exact Or.inl hmissing
  · exact Or.inr ⟨rightResult, hpresent, hevent⟩

theorem probEvent_right_le_missing_add_projected
    (project : alpha → Option beta) (left : ProbComp alpha) (right : ProbComp beta)
    (hrel : RelTriple left right fun leftResult rightResult =>
      project leftResult = none ∨ project leftResult = some rightResult)
    (event : beta → Prop) :
    Pr[event | right] ≤ Pr[fun result => project result = none | left] +
      Pr[fun result => ∃ value, project result = some value ∧ event value | left] := by
  exact (probEvent_right_le_projected_or_missing project left right hrel event).trans
    (probEvent_or_le _ _ _)

end SphincsSecurity.Concrete.FtsProbeSimulation
