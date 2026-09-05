import SphincsSecurity.Proof.FtsResidualCharge
import SphincsSecurity.Proof.AdaptiveRevealProbeCostExpectation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec ENNReal

def ProbeCacheCovered (parameter : PublicParameter)
    (state : AdaptiveRevealProbe.State Coordinate) (cache : SplitHashCache) : Prop :=
  ∀ probe : FtsSecretProbe, cache (.ordinary (probe.input parameter)) ≠ none →
    state.revealed (probe.index, probe.tree, probe.leafIdx) ≠ none ∨
      probe.candidate ∈ state.pending (probe.index, probe.tree, probe.leafIdx)

theorem probeCacheCovered_empty (parameter : PublicParameter) :
    ProbeCacheCovered parameter AdaptiveRevealProbe.State.empty emptySplitHashCache := by
  intro probe hcached
  exact (hcached rfl).elim

theorem ProbeCacheCovered.addPending {parameter : PublicParameter}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache) (coordinate : Coordinate) (candidate : Digest) :
    ProbeCacheCovered parameter (state.addPending coordinate candidate) cache := by
  intro probe hcached
  rcases hcovered probe hcached with hrevealed | hpending
  · exact Or.inl hrevealed
  · right
    by_cases heq : (probe.index, probe.tree, probe.leafIdx) = coordinate
    · simpa only [AdaptiveRevealProbe.State.addPending, heq, Function.update_self, Finset.mem_insert]
        using (Or.inr hpending : probe.candidate = candidate ∨ probe.candidate ∈ state.pending _)
    · simpa only [AdaptiveRevealProbe.State.addPending, Function.update_of_ne heq] using hpending

theorem ProbeCacheCovered.install {parameter : PublicParameter}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache) (coordinate : Coordinate) (value : Digest) :
    ProbeCacheCovered parameter (state.install coordinate value) cache := by
  intro probe hcached
  by_cases heq : (probe.index, probe.tree, probe.leafIdx) = coordinate
  · left
    simp only [AdaptiveRevealProbe.State.install, heq, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
  · simpa only [AdaptiveRevealProbe.State.install, Function.update_of_ne heq] using hcovered probe hcached

theorem ProbeCacheCovered.update_hidden {parameter : PublicParameter}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache) (coordinate : Coordinate) (answer : HashOutput) :
    ProbeCacheCovered parameter state (Function.update cache (.hiddenLeaf coordinate) (some answer)) := by
  intro probe hcached
  apply hcovered probe
  simpa only [Function.update_of_ne (by simp : SplitHashKey.ordinary (probe.input parameter) ≠
    SplitHashKey.hiddenLeaf coordinate)] using hcached

theorem ProbeCacheCovered.update_nonprobe {parameter : PublicParameter}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache) (input : HashInput) (answer : HashOutput)
    (hinput : ∀ probe : FtsSecretProbe, probe.input parameter ≠ input) :
    ProbeCacheCovered parameter state (Function.update cache (.ordinary input) (some answer)) := by
  intro probe hcached
  apply hcovered probe
  have hne : SplitHashKey.ordinary (probe.input parameter) ≠ .ordinary input :=
    fun heq => hinput probe (SplitHashKey.ordinary.inj heq)
  simpa only [Function.update_of_ne hne] using hcached

theorem ProbeCacheCovered.update_probed {parameter : PublicParameter}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache) (queried : FtsSecretProbe) (answer : HashOutput) :
    ProbeCacheCovered parameter
      (state.addPending (queried.index, queried.tree, queried.leafIdx) queried.candidate)
      (Function.update cache (.ordinary (queried.input parameter)) (some answer)) := by
  intro probe hcached
  by_cases heq : probe = queried
  · subst probe
    right
    simp only [AdaptiveRevealProbe.State.addPending, Function.update_self, Finset.mem_insert_self]
  · have hne : SplitHashKey.ordinary (probe.input parameter) ≠ .ordinary (queried.input parameter) := by
      intro h
      exact heq (FtsSecretProbe.input_injective parameter (SplitHashKey.ordinary.inj h))
    apply hcovered.addPending _ _ probe
    simpa only [Function.update_of_ne hne] using hcached

theorem ProbeCacheCovered.fresh_of_unrevealed_new {parameter : PublicParameter}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache) (probe : FtsSecretProbe)
    (hhidden : state.revealed (probe.index, probe.tree, probe.leafIdx) = none)
    (hnew : probe.candidate ∉ state.pending (probe.index, probe.tree, probe.leafIdx)) :
    cache (.ordinary (probe.input parameter)) = none := by
  by_contra hcached
  exact (hcovered probe hcached).elim (fun h => h hhidden) hnew

theorem ProbeCacheCovered.ordinary_probe_cached_merged {parameter : PublicParameter}
    {table : Coordinate → Digest} {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) (probe : FtsSecretProbe)
    (hcached : cache (.ordinary (probe.input parameter)) ≠ none) :
    mergedCache parameter table cache (probe.input parameter) ≠ none := by
  unfold mergedCache
  rw [decodeProbe?_input]
  dsimp only
  split_ifs with hhit
  · have hrevealed : state.revealed (probe.index, probe.tree, probe.leafIdx) ≠ none := by
      rcases hcovered probe hcached with h | hpending
      · exact h
      · exact (AdaptiveRevealProbe.not_mem_pending_of_tableHits_eq_false state table
          (probe.index, probe.tree, probe.leafIdx) hclean
          (by simpa only [← hhit] using hpending)).elim
    obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hrevealed
    obtain ⟨_, answer, hanswer, _⟩ := hsynced _ _ hvalue
    rw [hanswer]
    simp
  · exact hcached

def probeCachedInputs (parameter : PublicParameter) (cache : QueryCache HashSpec) : Set HashInput :=
  {input | cache input ≠ none ∧ ∃ probe : FtsSecretProbe, probe.input parameter = input}

theorem probeCachedInputs_finite (parameter : PublicParameter) {cache : QueryCache HashSpec}
    (hfinite : Finite cache) : (probeCachedInputs parameter cache).Finite :=
  hfinite.subset (fun _ h => h.1)

theorem ProbeCacheCovered.probeCachedInputs_subset_merged {parameter : PublicParameter}
    {table : Coordinate → Digest} {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache) :
    probeCachedInputs parameter (fun input => cache (.ordinary input)) ⊆
      probeCachedInputs parameter (mergedCache parameter table cache) := by
  rintro input ⟨hcached, probe, rfl⟩
  exact ⟨hcovered.ordinary_probe_cached_merged hclean hsynced probe hcached, probe, rfl⟩

theorem ProbeCacheCovered.probeCachedInputs_ncard_le_merged {parameter : PublicParameter}
    {table : Coordinate → Digest} {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache)
    (hfinite : Finite (mergedCache parameter table cache)) :
    (probeCachedInputs parameter (fun input => cache (.ordinary input))).ncard ≤
      (probeCachedInputs parameter (mergedCache parameter table cache)).ncard :=
  Set.ncard_le_ncard (hcovered.probeCachedInputs_subset_merged hclean hsynced)
    (probeCachedInputs_finite parameter hfinite)

theorem probeCachedInputs_cacheQuery_probe (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (probe : FtsSecretProbe) (answer : HashOutput) :
    probeCachedInputs parameter (cache.cacheQuery (probe.input parameter) answer) =
      insert (probe.input parameter) (probeCachedInputs parameter cache) := by
  ext input
  by_cases heq : input = probe.input parameter
  · rw [heq]
    simp only [probeCachedInputs, Set.mem_setOf_eq, QueryCache.cacheQuery_self,
      Set.mem_insert_iff, true_or, iff_true]
    exact ⟨by simp, probe, rfl⟩
  · simp only [probeCachedInputs, Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ heq,
      Set.mem_insert_iff, heq, false_or]

theorem probeCachedInputs_update_probed (parameter : PublicParameter) (cache : SplitHashCache)
    (probe : FtsSecretProbe) (answer : HashOutput) :
    probeCachedInputs parameter
        (fun input => Function.update cache (.ordinary (probe.input parameter)) (some answer) (.ordinary input)) =
      insert (probe.input parameter) (probeCachedInputs parameter (fun input => cache (.ordinary input))) := by
  have heq : (fun input => Function.update cache (.ordinary (probe.input parameter)) (some answer) (.ordinary input)) =
      QueryCache.cacheQuery (spec := HashSpec) (fun input => cache (.ordinary input))
        (probe.input parameter) answer := by
    funext input
    by_cases hi : input = probe.input parameter
    · rw [hi, Function.update_self, QueryCache.cacheQuery_self]
    · rw [Function.update_of_ne (fun h => hi (SplitHashKey.ordinary.inj h)),
        QueryCache.cacheQuery_of_ne _ _ hi]
  rw [heq, probeCachedInputs_cacheQuery_probe]

theorem ProbeCacheCovered.pendingCharge_le_cache_growth {parameter : PublicParameter}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache) (probe : FtsSecretProbe) (answer : HashOutput)
    (hhidden : state.revealed (probe.index, probe.tree, probe.leafIdx) = none)
    (hfinite : (probeCachedInputs parameter (fun input => cache (.ordinary input))).Finite) :
    (probeCachedInputs parameter (fun input => cache (.ordinary input))).ncard +
        AdaptiveRevealProbe.pendingProbeCharge state (probe.index, probe.tree, probe.leafIdx) probe.candidate ≤
      (probeCachedInputs parameter
        (fun input => Function.update cache (.ordinary (probe.input parameter)) (some answer) (.ordinary input))).ncard := by
  rw [probeCachedInputs_update_probed]
  by_cases hmem : probe.candidate ∈ state.pending (probe.index, probe.tree, probe.leafIdx)
  · rw [AdaptiveRevealProbe.pendingProbeCharge, if_pos hmem, Nat.add_zero]
    exact Set.ncard_le_ncard (Set.subset_insert _ _) (hfinite.insert _)
  · rw [AdaptiveRevealProbe.pendingProbeCharge, if_neg hmem]
    have hfresh := hcovered.fresh_of_unrevealed_new probe hhidden hmem
    have hnot : probe.input parameter ∉ probeCachedInputs parameter (fun input => cache (.ordinary input)) :=
      fun h => h.1 hfresh
    rw [Set.ncard_insert_of_notMem hnot hfinite]

noncomputable def ftsHashQueryCharge (parameter : PublicParameter)
    (_cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  open Classical in
  if ∃ probe : FtsSecretProbe, probe.input parameter = input then 1 else 0

theorem probeCachedInputs_cacheQuery_nonprobe (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput)
    (hinput : ¬ ∃ probe : FtsSecretProbe, probe.input parameter = input) :
    probeCachedInputs parameter (cache.cacheQuery input answer) = probeCachedInputs parameter cache := by
  ext other
  by_cases heq : other = input
  · rw [heq]
    simp only [probeCachedInputs, Set.mem_setOf_eq, hinput, and_false]
  · simp only [probeCachedInputs, Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ heq]

theorem probeCachedInputs_cacheQuery_ncard_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput) :
    ((probeCachedInputs parameter (cache.cacheQuery input answer)).ncard : ℝ≥0∞) ≤
      (probeCachedInputs parameter cache).ncard + ftsHashQueryCharge parameter cache input := by
  classical
  unfold ftsHashQueryCharge
  split_ifs with hprobe
  · obtain ⟨probe, rfl⟩ := hprobe
    rw [probeCachedInputs_cacheQuery_probe]
    exact_mod_cast Set.ncard_insert_le (probe.input parameter) (probeCachedInputs parameter cache)
  · rw [probeCachedInputs_cacheQuery_nonprobe parameter cache input answer hprobe, add_zero]

theorem expected_probeCachedInputs_le_queryCharge {α : Type}
    (parameter : PublicParameter) (computation : OracleComp OracleWorld α) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run ∅] *
      ((probeCachedInputs parameter result.2).ncard : ℝ≥0∞)) ≤
      expectedQueryCharge (ftsHashQueryCharge parameter) computation ∅ := by
  let potential : QueryCache HashSpec → ℝ≥0∞ := fun cache => (probeCachedInputs parameter cache).ncard
  have hstep (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
      (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) ≤
        potential cache + hashQueryCharge (ftsHashQueryCharge parameter) cache query := by
    apply expected_potential_romImpl_le_charge
    · intro before hbefore input hfresh
      calc
        _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (potential before + ftsHashQueryCharge parameter before input) :=
          ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl
            (probeCachedInputs_cacheQuery_ncard_le parameter before input answer)
        _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
    · exact hfinite
  have h := expected_potential_simulateQ_le_queryCharge potential (ftsHashQueryCharge parameter)
    hstep computation ∅ finite_empty
  have hempty : probeCachedInputs parameter (∅ : QueryCache HashSpec) = ∅ := by
    ext input
    simp only [probeCachedInputs, Set.mem_setOf_eq, QueryCache.empty_apply, ne_eq, not_true_eq_false,
      false_and, Set.mem_empty_iff_false]
  simpa only [potential, hempty, Set.ncard_empty, Nat.cast_zero, zero_add] using h

theorem ftsHashQueryCharge_mul_two_le_residual (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) :
    ftsHashQueryCharge secretKey.parameter cache input * 2 ≤
      residualPrimitiveQueryCharge secretKey cache input := by
  classical
  unfold ftsHashQueryCharge
  split_ifs with hprobe
  · obtain ⟨probe, rfl⟩ := hprobe
    rw [one_mul]
    exact residualPrimitiveQueryCharge_ge_two_ftsProbe secretKey cache probe
  · rw [zero_mul]
    exact bot_le

end SphincsSecurity.Concrete.FtsProbeSimulation
