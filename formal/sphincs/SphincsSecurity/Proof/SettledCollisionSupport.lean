import SphincsSecurity.Proof.SettledCollisionMonitor

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def HistoryInvariant (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (history : History) : Prop :=
  history.hit = false → ∀ input answer, input ∉ history.unsettled → cache input = some answer →
    ∃ position, AtPosition secretKey.parameter input position ∧
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position ∧
      truncateHash answer ≠
        honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret position

theorem historyInvariant_initial (secretKey : SecretKey) :
    HistoryInvariant secretKey ∅ initialHistory := by
  intro _ input answer _ hcached
  simp at hcached

theorem historyInvariant_fresh (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (history : History) (input : HashInput) (answer : HashOutput)
    (hinvariant : HistoryInvariant secretKey cache history) (hfresh : cache input = none) :
    HistoryInvariant secretKey (cache.cacheQuery input answer)
      (advance secretKey cache history (.inr input) answer) := by
  intro hfalse other otherAnswer hnot hcached
  have hflags : history.hit = false ∧ ¬ Collision secretKey cache input answer := by
    simpa only [advance, queryHit, Bool.or_eq_false_iff, decide_eq_false_iff_not] using hfalse
  have hle := le_cacheQuery (answer := answer) hfresh
  have hnotOld : other ∉ history.unsettled := by
    intro hmem
    apply hnot
    simp only [advance]
    split_ifs
    · exact Finset.mem_insert_of_mem hmem
    · exact hmem
  by_cases heq : other = input
  · subst other
    have hsettledInput : SettledInput secretKey cache input := by
      by_contra hnone
      simp [advance, hfresh, hnone] at hnot
    obtain ⟨position, hat, hsettled⟩ := hsettledInput
    have hanswer : otherAnswer = answer := by
      simpa only [QueryCache.cacheQuery_self, Option.some.injEq] using hcached.symm
    subst otherAnswer
    refine ⟨position, hat, hsettled.mono hle, ?_⟩
    rw [honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) hsettled]
    intro hvalue
    exact hflags.2 ⟨hfresh, position, hat, hsettled, hvalue⟩
  · have hcachedOld : cache other = some otherAnswer := by
      rwa [QueryCache.cacheQuery_of_ne _ _ heq] at hcached
    obtain ⟨position, hat, hsettled, hne⟩ := hinvariant hflags.1 other otherAnswer hnotOld hcachedOld
    refine ⟨position, hat, hsettled.mono hle, ?_⟩
    rwa [honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) hsettled]

theorem historyInvariant_advance (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (history : History) (query : OracleWorld.Domain)
    (result : OracleWorld.Range query × QueryCache HashSpec)
    (hinvariant : HistoryInvariant secretKey cache history)
    (hresult : result ∈ support ((romImpl query).run cache)) :
    HistoryInvariant secretKey result.2 (advance secretKey cache history query result.1) := by
  cases query with
  | inl input =>
      change unifSpec.Range input × QueryCache HashSpec at result
      have hquery : (romImpl (.inl input)).run cache =
          (fun answer => (answer, cache)) <$> (liftM (unifSpec.query input) : ProbComp _) := rfl
      rw [hquery] at hresult
      change result ∈ support ((fun answer : Fin (input + 1) => (answer, cache)) <$>
        (liftM (unifSpec.query input) : ProbComp (Fin (input + 1)))) at hresult
      rw [support_map] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      simpa only [advance, queryHit, Bool.or_false] using hinvariant
  | inr input =>
      change HashOutput × QueryCache HashSpec at result
      change result ∈ support ((randomOracle input).run cache) at hresult
      by_cases hfresh : cache input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map] at hresult
        obtain ⟨answer, _, rfl⟩ := hresult
        exact historyInvariant_fresh secretKey cache history input answer hinvariant hfresh
      · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
        rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer,
          support_pure, Set.mem_singleton_iff] at hresult
        subst result
        simpa only [advance, queryHit, Collision, hfresh, false_and, decide_false,
          Bool.or_false, if_false] using hinvariant

theorem historyInvariant_runMonitor (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (history : History)
    (hinvariant : HistoryInvariant secretKey cache history)
    (result : (α × QueryCache HashSpec) × History)
    (hresult : result ∈ support (runMonitor secretKey computation cache history)) :
    HistoryInvariant secretKey result.1.2 result.2 := by
  induction computation using OracleComp.inductionOn generalizing cache history with
  | pure value =>
      simp only [runMonitor, OracleComp.construct_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hinvariant
  | query_bind query next ih =>
      rw [runMonitor, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨response, hresponse, hresult⟩ := hresult
      exact ih response.1 response.2 _
        (historyInvariant_advance secretKey cache history query response hinvariant hresponse) hresult

theorem badOnInputs_implies_hit_or_unsettled {secretKey : SecretKey}
    {cache : QueryCache HashSpec} {history : History} {inputs : Set HashInput}
    (hinvariant : HistoryInvariant secretKey cache history)
    (hbad : BadOnInputs secretKey cache inputs) :
    history.hit = true ∨ BadOnInputs secretKey cache (inputs ∩ ↑history.unsettled) := by
  by_cases hhit : history.hit = true
  · exact Or.inl hhit
  · right
    obtain ⟨position, input, ax, ay, hinput, hsettled, hat, hne, hx, hy, hvalue⟩ := hbad
    refine ⟨position, input, ax, ay, ⟨hinput, ?_⟩, hsettled, hat, hne, hx, hy, hvalue⟩
    by_contra hnot
    obtain ⟨other, hother, _, havoid⟩ := hinvariant (Bool.eq_false_iff.mpr hhit) input ax hnot hx
    rw [atPosition_unique secretKey.parameter hother hat] at havoid
    apply havoid
    change truncateHash ax = truncateHash
      (fromCache cache (cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position))
    simpa only [fromCache, hy, Option.getD_some] using hvalue

theorem probEvent_badOnInputs_le_charge_add_unsettled (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α)
    (guard : α × QueryCache HashSpec → Prop)
    (inputs : α × QueryCache HashSpec → Set HashInput) :
    Pr[fun result => guard result ∧ BadOnInputs secretKey result.2 (inputs result) |
      (simulateQ romImpl computation).run ∅] ≤
    expectedQueryCharge (queryCharge secretKey) computation ∅ * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      Pr[fun result => guard result.1 ∧ BadOnInputs secretKey result.1.2
        (inputs result.1 ∩ ↑result.2.unsettled) | runMonitor secretKey computation ∅ initialHistory] := by
  rw [← runMonitor_project secretKey computation ∅ initialHistory, probEvent_map]
  calc
    _ ≤ Pr[fun result => result.2.hit = true ∨ (guard result.1 ∧ BadOnInputs secretKey result.1.2
        (inputs result.1 ∩ ↑result.2.unsettled)) | runMonitor secretKey computation ∅ initialHistory] := by
      apply probEvent_mono
      rintro result hresult ⟨hguard, hbad⟩
      rcases badOnInputs_implies_hit_or_unsettled
        (historyInvariant_runMonitor secretKey computation ∅ initialHistory
          (historyInvariant_initial secretKey) result hresult) hbad with hhit | hunsettled
      · exact Or.inl hhit
      · exact Or.inr ⟨hguard, hunsettled⟩
    _ ≤ _ := (probEvent_or_le _ _ _).trans
      (add_le_add (probEvent_runMonitor_hit_le_queryCharge secretKey computation ∅) le_rfl)

end SphincsSecurity.Concrete.SettledCollision
