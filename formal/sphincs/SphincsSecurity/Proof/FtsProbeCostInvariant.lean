import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.AdaptiveRevealProbeCostBind
import SphincsSecurity.Proof.FtsProbeCacheCharge
import SphincsSecurity.Proof.FtsProbeSigner
import SphincsSecurity.Proof.OtsProbeRealization

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec ENNReal
open _root_.OracleComp

abbrev splitProbeInputs (parameter : PublicParameter) (cache : SplitHashCache) : Set HashInput :=
  probeCachedInputs parameter (fun input => cache (.ordinary input))

def ProbeCostInvariant {α : Type} (parameter : PublicParameter)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α) : Prop :=
  ∀ table state cache fuel, ProbeCacheCovered parameter state cache → (splitProbeInputs parameter cache).Finite →
    ∀ hit finalState value finalCache cost,
      (.done hit finalState (value, finalCache), cost) ∈ support
        (AdaptiveRevealProbe.runCharged table state fuel (computation.run cache)) →
      ProbeCacheCovered parameter finalState finalCache ∧ (splitProbeInputs parameter finalCache).Finite ∧
        (splitProbeInputs parameter cache).ncard + cost ≤ (splitProbeInputs parameter finalCache).ncard

theorem ProbeCostInvariant.pure {α : Type} (parameter : PublicParameter) (value : α) :
    ProbeCostInvariant parameter (pure value) := by
  intro table state cache fuel hcovered hfinite hit finalState result finalCache cost hresult
  simp only [StateT.run_pure, AdaptiveRevealProbe.runCharged, OracleComp.construct_pure,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq, AdaptiveRevealProbe.DetailedResult.done.injEq] at hresult
  obtain ⟨⟨_, rfl, ⟨_, rfl⟩⟩, rfl⟩ := hresult
  exact ⟨hcovered, hfinite, by omega⟩

theorem ProbeCostInvariant.bind {α β : Type} {parameter : PublicParameter}
    {left : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) β}
    (hleft : ProbeCostInvariant parameter left) (hnext : ∀ value, ProbeCostInvariant parameter (next value)) :
    ProbeCostInvariant parameter (left >>= next) := by
  intro table state cache fuel hcovered hfinite hit finalState value finalCache cost hresult
  rw [StateT.run_bind] at hresult
  obtain ⟨middleState, ⟨middleValue, middleCache⟩, middleFuel, leftCost, rightCost,
      _, hfirst, hsecond, hcost⟩ :=
    AdaptiveRevealProbe.runCharged_bind_done_support table (left.run cache)
      (fun result => (next result.1).run result.2) state fuel hit finalState (value, finalCache) cost hresult
  obtain ⟨hcoveredMiddle, hfiniteMiddle, hcountFirst⟩ :=
    hleft table state cache fuel hcovered hfinite _ middleState middleValue middleCache leftCost hfirst
  obtain ⟨hcoveredFinal, hfiniteFinal, hcountSecond⟩ :=
    hnext middleValue table middleState middleCache middleFuel hcoveredMiddle hfiniteMiddle
      hit finalState value finalCache rightCost hsecond
  exact ⟨hcoveredFinal, hfiniteFinal, by omega⟩

theorem ProbeCostInvariant.map {α β : Type} {parameter : PublicParameter}
    {computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α}
    (hcomputation : ProbeCostInvariant parameter computation) (transform : α → β) :
    ProbeCostInvariant parameter (transform <$> computation) := by
  rw [map_eq_bind_pure_comp]
  exact hcomputation.bind fun value => ProbeCostInvariant.pure parameter (transform value)

theorem probeCostInvariant_of_stateFree {α : Type} (parameter : PublicParameter)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (hstateFree : StateFree computation)
    (hentries : ∀ cache result, result ∈ support (computation.run cache) → ∀ probe : FtsSecretProbe,
      result.2 (.ordinary (probe.input parameter)) = cache (.ordinary (probe.input parameter))) :
    ProbeCostInvariant parameter computation := by
  intro table state cache fuel hcovered hfinite hit finalState value finalCache cost hresult
  have hsupport := AdaptiveRevealProbe.runCharged_done_mem_support table state finalState fuel
    (computation.run cache) hit (value, finalCache) cost hresult
  obtain ⟨rfl, rfl⟩ := AdaptiveRevealProbe.runCharged_done_stateFree table state finalState fuel
    (computation.run cache) (hstateFree cache) hit (value, finalCache) cost hresult
  have hsets : splitProbeInputs parameter finalCache = splitProbeInputs parameter cache := by
    ext input
    constructor
    · rintro ⟨hcached, probe, rfl⟩
      have he := hentries cache (value, finalCache) hsupport probe
      dsimp only at he
      exact ⟨by simpa only [he] using hcached, probe, rfl⟩
    · rintro ⟨hcached, probe, rfl⟩
      have he := hentries cache (value, finalCache) hsupport probe
      dsimp only at he
      exact ⟨by simpa only [he] using hcached, probe, rfl⟩
  refine ⟨?_, by simpa only [hsets] using hfinite, by rw [hsets, Nat.add_zero]⟩
  intro probe hcached
  apply hcovered probe
  rwa [← hentries cache (value, finalCache) hsupport probe]

theorem probeCostInvariant_splitHashQuery_hidden (parameter : PublicParameter) (coordinate : Coordinate) :
    ProbeCostInvariant parameter (splitHashQuery (.hiddenLeaf coordinate)) := by
  apply probeCostInvariant_of_stateFree parameter _ (splitHashQuery_stateFree _)
  intro cache result hresult probe
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.hiddenLeaf coordinate) with
  | some answer =>
      simp only [hlookup, support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
  | none =>
      simp only [hlookup, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      exact Function.update_of_ne (by simp : SplitHashKey.ordinary (probe.input parameter) ≠
        SplitHashKey.hiddenLeaf coordinate) (some answer) cache

theorem probeCostInvariant_splitHashQuery_nonprobe (parameter : PublicParameter) (input : HashInput)
    (hinput : ∀ probe : FtsSecretProbe, probe.input parameter ≠ input) :
    ProbeCostInvariant parameter (splitHashQuery (.ordinary input)) := by
  apply probeCostInvariant_of_stateFree parameter _ (splitHashQuery_stateFree _)
  intro cache result hresult probe
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache (.ordinary input) with
  | some answer =>
      simp only [hlookup, support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
  | none =>
      simp only [hlookup, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      exact Function.update_of_ne (fun heq => hinput probe (SplitHashKey.ordinary.inj heq)) (some answer) cache

theorem probeCostInvariant_splitUniformImpl (parameter : PublicParameter) (n : unifSpec.Domain) :
    ProbeCostInvariant parameter (splitUniformImpl n) := by
  apply probeCostInvariant_of_stateFree parameter _ (splitUniformImpl_stateFree n)
  intro cache result hresult probe
  unfold splitUniformImpl at hresult
  rw [StateT.run_liftM, mem_support_bind_iff] at hresult
  obtain ⟨answer, _, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  rw [hresult]

theorem no_probe_of_ordinary_all (parameter : PublicParameter) (input : HashInput)
    (hordinary : ∀ table : Coordinate → Digest, IsOrdinaryInput parameter table input) :
    ∀ probe : FtsSecretProbe, probe.input parameter ≠ input := by
  intro probe heq
  exact hordinary (fun _ => probe.candidate) probe
    ((decodeProbe?_eq_some_iff parameter input probe).mpr heq) rfl

theorem probeCostInvariant_simulateQ_ordinaryHashImpl {α : Type} (parameter : PublicParameter)
    (computation : OracleComp HashSpec α)
    (hordinary : ∀ table : Coordinate → Digest, OrdinaryOnly parameter table computation) :
    ProbeCostInvariant parameter (simulateQ ordinaryHashImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure]
      exact ProbeCostInvariant.pure parameter value
  | query_bind input next ih =>
      have hstep (table : Coordinate → Digest) : IsOrdinaryInput parameter table input := by
        have hbound := hordinary table
        rw [OrdinaryOnly, isQueryBoundP_query_bind_iff] at hbound
        by_contra hnot
        simpa [NonOrdinaryInput, hnot] using hbound.1
      rw [simulateQ_query_bind]
      apply (probeCostInvariant_splitHashQuery_nonprobe parameter input
        (no_probe_of_ordinary_all parameter input hstep)).bind
      intro output
      apply ih output
      intro table
      have hbound := hordinary table
      rw [OrdinaryOnly, isQueryBoundP_query_bind_iff] at hbound
      simpa [OrdinaryOnly, NonOrdinaryInput, hstep table] using hbound.2 output

theorem probeCostInvariant_simulateQ_splitRomImpl {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α)
    (hordinary : ∀ table : Coordinate → Digest, RomOrdinaryOnly parameter table computation) :
    ProbeCostInvariant parameter (simulateQ splitRomImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure]
      exact ProbeCostInvariant.pure parameter value
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      cases input with
      | inl n =>
          apply (probeCostInvariant_splitUniformImpl parameter n).bind
          intro output
          apply ih output
          intro table
          have hbound := hordinary table
          rw [RomOrdinaryOnly, isQueryBoundP_query_bind_iff] at hbound
          simpa [RomOrdinaryOnly] using hbound.2 output
      | inr input =>
          have hstep (table : Coordinate → Digest) : IsOrdinaryInput parameter table input := by
            have hbound := hordinary table
            rw [RomOrdinaryOnly, isQueryBoundP_query_bind_iff] at hbound
            by_contra hnot
            simpa [NonOrdinaryInput, hnot] using hbound.1
          apply (probeCostInvariant_splitHashQuery_nonprobe parameter input
            (no_probe_of_ordinary_all parameter input hstep)).bind
          intro output
          apply ih output
          intro table
          have hbound := hordinary table
          rw [RomOrdinaryOnly, isQueryBoundP_query_bind_iff] at hbound
          simpa [RomOrdinaryOnly, NonOrdinaryInput, hstep table] using hbound.2 output

theorem probeCostInvariant_sequenceFin {α : Type} {n : Nat} (parameter : PublicParameter)
    (computation : Fin n → StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (hcomputation : ∀ position, ProbeCostInvariant parameter (computation position)) :
    ProbeCostInvariant parameter (sequenceFin computation) := by
  induction n with
  | zero => exact ProbeCostInvariant.pure parameter (Fin.elim0 : Fin 0 → α)
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomputation 0).bind fun head =>
        (ih (fun position => computation position.succ) (fun position => hcomputation position.succ)).bind
          fun tail => ProbeCostInvariant.pure parameter (Fin.cases head tail : Fin (n + 1) → α)

theorem splitHashQuery_support_cache (key : SplitHashKey) (cache finalCache : SplitHashCache)
    (output : HashOutput) (hresult : (output, finalCache) ∈ support ((splitHashQuery key).run cache)) :
    (finalCache = cache ∧ cache key = some output) ∨
      finalCache = Function.update cache key (some output) := by
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache key with
  | some answer =>
      simp only [hlookup, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hresult
      exact Or.inl ⟨hresult.2, by simpa only [hresult.1] using hlookup⟩
  | none =>
      simp only [hlookup, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hresult
      exact Or.inr (by simpa only [hresult.1] using hresult.2)

theorem ProbeCacheCovered.update_revealed {parameter : PublicParameter}
    {state : AdaptiveRevealProbe.State Coordinate} {cache : SplitHashCache}
    (hcovered : ProbeCacheCovered parameter state cache) (queried : FtsSecretProbe) (answer : HashOutput)
    (hrevealed : state.revealed (queried.index, queried.tree, queried.leafIdx) ≠ none) :
    ProbeCacheCovered parameter state
      (Function.update cache (.ordinary (queried.input parameter)) (some answer)) := by
  intro probe hcached
  by_cases heq : probe = queried
  · rw [heq]
    exact Or.inl hrevealed
  · apply hcovered probe
    have hne : SplitHashKey.ordinary (probe.input parameter) ≠ .ordinary (queried.input parameter) :=
      fun h => heq (FtsSecretProbe.input_injective parameter (SplitHashKey.ordinary.inj h))
    simpa only [Function.update_of_ne hne] using hcached

end SphincsSecurity.Concrete.FtsProbeSimulation
