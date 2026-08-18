import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.ProbComp
import VCVio.ProgramLogic.Unary.HoareTriple
import VCVio.ProgramLogic.Relational.Basic

open OracleSpec OracleComp ENNReal

namespace XmssSecurity

open OracleComp.ProgramLogic.Relational

/-- A coupling that pointwise decreases a nonnegative cost also decreases its expectation. -/
theorem expectedCost_le_of_relTriple
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    (left : OracleComp spec₁ α) (right : OracleComp spec₂ β)
    (relation : α → β → Prop) (leftCost : α → ENNReal)
    (rightCost : β → ENNReal)
    (hrel : RelTriple left right relation)
    (hcost : ∀ leftResult rightResult,
      relation leftResult rightResult →
        rightCost rightResult ≤ leftCost leftResult) :
    (∑' result, Pr[= result | right] * rightCost result) ≤
      ∑' result, Pr[= result | left] * leftCost result := by
  obtain ⟨coupling, hcoupled⟩ := (relTriple_iff_relWP).1 hrel
  have hleft : evalDist (Prod.fst <$> coupling.1) = evalDist left :=
    coupling.2.map_fst
  have hright : evalDist (Prod.snd <$> coupling.1) = evalDist right :=
    coupling.2.map_snd
  calc
    (∑' result, Pr[= result | right] * rightCost result) =
        ∑' result, Pr[= result | Prod.snd <$> coupling.1] *
          rightCost result := by
      apply tsum_congr
      intro result
      rw [probOutput_def, probOutput_def, hright]
    _ = ∑' result, Pr[= result | coupling.1] * rightCost result.2 :=
      tsum_probOutput_map_mul coupling.1 Prod.snd rightCost
    _ ≤ ∑' result, Pr[= result | coupling.1] * leftCost result.1 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support coupling.1
      · gcongr
        exact hcost result.1 result.2 (hcoupled result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp
    _ = ∑' result, Pr[= result | Prod.fst <$> coupling.1] *
        leftCost result :=
      (tsum_probOutput_map_mul coupling.1 Prod.fst leftCost).symm
    _ = ∑' result, Pr[= result | left] * leftCost result := by
      apply tsum_congr
      intro result
      rw [probOutput_def, probOutput_def, hleft]

/-- A coupling that bounds the right cost by a left cost and a right-side error cost
also bounds its expectation by the sum of their expectations. -/
theorem expectedCost_le_add_of_relTriple
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    (left : OracleComp spec₁ α) (right : OracleComp spec₂ β)
    (relation : α → β → Prop) (leftCost : α → ENNReal)
    (rightCost rightError : β → ENNReal)
    (hrel : RelTriple left right relation)
    (hcost : ∀ leftResult rightResult,
      relation leftResult rightResult →
        rightCost rightResult ≤ leftCost leftResult + rightError rightResult) :
    (∑' result, Pr[= result | right] * rightCost result) ≤
      (∑' result, Pr[= result | left] * leftCost result) +
        ∑' result, Pr[= result | right] * rightError result := by
  obtain ⟨coupling, hcoupled⟩ := (relTriple_iff_relWP).1 hrel
  have hleft : evalDist (Prod.fst <$> coupling.1) = evalDist left :=
    coupling.2.map_fst
  have hright : evalDist (Prod.snd <$> coupling.1) = evalDist right :=
    coupling.2.map_snd
  calc
    (∑' result, Pr[= result | right] * rightCost result) =
        ∑' result, Pr[= result | Prod.snd <$> coupling.1] *
          rightCost result := by
      apply tsum_congr
      intro result
      rw [probOutput_def, probOutput_def, hright]
    _ = ∑' result, Pr[= result | coupling.1] * rightCost result.2 :=
      tsum_probOutput_map_mul coupling.1 Prod.snd rightCost
    _ ≤ ∑' result, Pr[= result | coupling.1] *
        (leftCost result.1 + rightError result.2) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support coupling.1
      · gcongr
        exact hcost result.1 result.2 (hcoupled result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp
    _ = (∑' result, Pr[= result | coupling.1] * leftCost result.1) +
        ∑' result, Pr[= result | coupling.1] * rightError result.2 := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
    _ = (∑' result, Pr[= result | Prod.fst <$> coupling.1] *
          leftCost result) +
        ∑' result, Pr[= result | Prod.snd <$> coupling.1] *
          rightError result := by
      rw [tsum_probOutput_map_mul coupling.1 Prod.fst leftCost,
        tsum_probOutput_map_mul coupling.1 Prod.snd rightError]
    _ = (∑' result, Pr[= result | left] * leftCost result) +
        ∑' result, Pr[= result | right] * rightError result := by
      congr 1 <;> apply tsum_congr <;> intro result <;>
        rw [probOutput_def, probOutput_def]
      · rw [hleft]
      · rw [hright]

/-- The expected number of matching source queries after interpreting a computation in a
stateful probabilistic oracle implementation. -/
noncomputable def expectedSimulatedQueryCount
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp spec α) (initialState : state) : ENNReal :=
  (OracleComp.recOn (motive := fun _ => state → ENNReal) computation
    (fun _ _ => 0)
    (fun input _ continuationCounts currentState =>
      (if predicate input then 1 else 0) +
        ∑' result, Pr[= result | (implementation input).run currentState] *
          continuationCounts result.1 result.2)) initialState

@[simp]
theorem expectedSimulatedQueryCount_pure
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (value : α) (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
      (pure value : OracleComp spec α) initialState = 0 := by
  rfl

@[simp]
theorem expectedSimulatedQueryCount_query_bind
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
    (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (liftM (spec.query input) >>= next) initialState =
      (if predicate input then 1 else 0) +
        ∑' result, Pr[= result | (implementation input).run initialState] *
          expectedSimulatedQueryCount implementation predicate
            (next result.1) result.2 := by
  rfl

@[simp]
theorem expectedSimulatedQueryCount_query
    {ι : Type} {spec : OracleSpec ι} {state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (input : spec.Domain) (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (liftM (spec.query input)) initialState =
      if predicate input then 1 else 0 := by
  rw [← bind_pure (liftM (spec.query input) : OracleComp spec _)]
  rw [expectedSimulatedQueryCount_query_bind]
  simp

/-- A pathwise source-query bound controls the expected count in every stateful implementation. -/
theorem expectedSimulatedQueryCount_le_of_isQueryBoundP
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp spec α) (initialState : state) (q : Nat)
    (hbound : computation.IsQueryBoundP predicate q) :
    expectedSimulatedQueryCount implementation predicate computation initialState ≤ q := by
  induction computation using OracleComp.inductionOn generalizing initialState q with
  | pure value => simp
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [expectedSimulatedQueryCount_query_bind]
      by_cases hinput : predicate input
      · simp only [hinput, if_true]
        have hqpos : 0 < q := hbound.1.resolve_left (not_not.mpr hinput)
        have hq : 1 ≤ q := hqpos
        calc
          1 + ∑' result, Pr[= result | (implementation input).run initialState] *
                expectedSimulatedQueryCount implementation predicate
                  (next result.1) result.2 ≤
              1 + ∑' result, Pr[= result | (implementation input).run initialState] *
                (q - 1 : Nat) := by
                  gcongr with result
                  exact ih result.1 result.2 (q - 1)
                    (by simpa [hinput] using hbound.2 result.1)
          _ = 1 + (∑' result,
                Pr[= result | (implementation input).run initialState]) *
                  (q - 1 : Nat) := by
                    rw [ENNReal.tsum_mul_right]
          _ ≤ 1 + 1 * (q - 1 : Nat) := by
                  gcongr
                  exact tsum_probOutput_le_one
          _ = q := by
                  rw [one_mul, ← Nat.cast_one, ← Nat.cast_add,
                    Nat.add_sub_of_le hq]
      · simp only [hinput, if_false, zero_add]
        calc
          ∑' result, Pr[= result | (implementation input).run initialState] *
                expectedSimulatedQueryCount implementation predicate
                  (next result.1) result.2 ≤
              ∑' result, Pr[= result | (implementation input).run initialState] * q := by
                  apply ENNReal.tsum_le_tsum
                  intro result
                  gcongr
                  exact ih result.1 result.2 q
                    (by simpa [hinput] using hbound.2 result.1)
          _ = (∑' result,
                Pr[= result | (implementation input).run initialState]) * q := by
                  rw [ENNReal.tsum_mul_right]
          _ ≤ 1 * q := by
                  gcongr
                  exact tsum_probOutput_le_one
          _ = q := one_mul _

/-- Enlarging the source predicate can only increase its expected simulated count. -/
theorem expectedSimulatedQueryCount_mono
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (left right : spec.Domain → Prop) [DecidablePred left] [DecidablePred right]
    (hsubset : ∀ input, left input → right input)
    (computation : OracleComp spec α) (initialState : state) :
    expectedSimulatedQueryCount implementation left computation initialState ≤
      expectedSimulatedQueryCount implementation right computation initialState := by
  induction computation using OracleComp.recOn generalizing initialState with
  | pure value =>
      change expectedSimulatedQueryCount implementation left
          (pure value : OracleComp spec α) initialState ≤
        expectedSimulatedQueryCount implementation right
          (pure value : OracleComp spec α) initialState
      simp
  | queryBind input next ih =>
      change (if left input then 1 else 0) +
          ∑' result, Pr[= result | (implementation input).run initialState] *
            expectedSimulatedQueryCount implementation left
              (next result.1) result.2 ≤
        (if right input then 1 else 0) +
          ∑' result, Pr[= result | (implementation input).run initialState] *
            expectedSimulatedQueryCount implementation right
              (next result.1) result.2
      have hindicator : (if left input then (1 : ENNReal) else 0) ≤
          if right input then 1 else 0 := by
        by_cases hleft : left input
        · simp [hleft, hsubset input hleft]
        · simp [hleft]
      apply add_le_add hindicator
      apply ENNReal.tsum_le_tsum
      intro result
      gcongr
      exact ih result.1 result.2

/-- Expected simulated query count decomposes into the head count plus the expected continuation
count. -/
theorem expectedSimulatedQueryCount_bind
    {ι : Type} {spec : OracleSpec ι} {α β state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (head : OracleComp spec α) (continuation : α → OracleComp spec β)
    (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (head >>= continuation) initialState =
      expectedSimulatedQueryCount implementation predicate head initialState +
        ∑' result, Pr[= result | (simulateQ implementation head).run initialState] *
          expectedSimulatedQueryCount implementation predicate
            (continuation result.1) result.2 := by
  induction head using OracleComp.inductionOn generalizing initialState with
  | pure value =>
      simp [simulateQ_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      rw [bind_assoc, expectedSimulatedQueryCount_query_bind,
        expectedSimulatedQueryCount_query_bind]
      simp_rw [ih, mul_add]
      rw [ENNReal.tsum_add]
      rw [simulateQ_bind, StateT.run_bind, simulateQ_query,
        tsum_probOutput_bind_mul]
      simp only [OracleQuery.input_query, OracleQuery.cont_query]
      rw [id_map]
      ac_rfl

theorem expectedSimulatedQueryCount_map
    {index : Type} {spec : OracleSpec index} {α β state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (project : α → β) (computation : OracleComp spec α)
    (initialState : state) :
    expectedSimulatedQueryCount implementation predicate
        (project <$> computation) initialState =
      expectedSimulatedQueryCount implementation predicate computation
        initialState := by
  rw [map_eq_bind_pure_comp]
  change expectedSimulatedQueryCount implementation predicate
      (computation >>= fun value => pure (project value)) initialState = _
  calc
    _ = expectedSimulatedQueryCount implementation predicate computation
          initialState +
        ∑' result,
          Pr[= result | (simulateQ implementation computation).run initialState] *
            expectedSimulatedQueryCount implementation predicate
              (pure (project result.1)) result.2 :=
      expectedSimulatedQueryCount_bind implementation predicate computation
        (fun value => pure (project value)) initialState
    _ = _ := by simp

/-- Counting selected outer queries through a composed oracle implementation is bounded by counting all selected inner queries used to interpret the outer computation. -/
theorem expectedSimulatedQueryCount_compose_le
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {α state : Type}
    (inner : QueryImpl spec₂ (StateT state ProbComp))
    (middle : QueryImpl spec₁ (OracleComp spec₂))
    (outerPredicate : spec₁.Domain → Prop) [DecidablePred outerPredicate]
    (innerPredicate : spec₂.Domain → Prop) [DecidablePred innerPredicate]
    (hquery : ∀ input initialState,
      (if outerPredicate input then (1 : ENNReal) else 0) ≤
        expectedSimulatedQueryCount inner innerPredicate
          (middle input) initialState)
    (computation : OracleComp spec₁ α) (initialState : state) :
    expectedSimulatedQueryCount (inner ∘ₛ middle) outerPredicate
        computation initialState ≤
      expectedSimulatedQueryCount inner innerPredicate
        (simulateQ middle computation) initialState := by
  induction computation using OracleComp.inductionOn generalizing initialState with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind, simulateQ_bind,
        simulateQ_query, expectedSimulatedQueryCount_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map,
        QueryImpl.apply_compose]
      apply add_le_add (hquery input initialState)
      apply ENNReal.tsum_le_tsum
      intro result
      gcongr
      exact ih result.1 result.2

/-- A resource that grows by at most one on each matching interpreted query has expected final
value at most its initial value plus the expected matching-query count. -/
theorem expectedResource_le_initial_add_expectedSimulatedQueryCount
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (resource : state → ENNReal)
    (hstep : ∀ input initialState result,
      result ∈ support ((implementation input).run initialState) →
        resource result.2 ≤ resource initialState +
          if predicate input then 1 else 0)
    (computation : OracleComp spec α) (initialState : state) :
    (∑' result,
      Pr[= result | (simulateQ implementation computation).run initialState] *
        resource result.2) ≤
      resource initialState +
        expectedSimulatedQueryCount implementation predicate computation initialState := by
  induction computation using OracleComp.inductionOn generalizing initialState with
  | pure value =>
      simp [simulateQ_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_query,
        tsum_probOutput_bind_mul]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map,
        expectedSimulatedQueryCount_query_bind]
      let head := (implementation input).run initialState
      let indicator : ENNReal := if predicate input then 1 else 0
      have hhead :
          (∑' result, Pr[= result | head] * resource result.2) ≤
            resource initialState + indicator := by
        calc
          _ ≤ ∑' result, Pr[= result | head] *
                (resource initialState + indicator) := by
              apply ENNReal.tsum_le_tsum
              intro result
              by_cases hresult : result ∈ support head
              · exact mul_le_mul_right (hstep input initialState result hresult) _
              · rw [probOutput_eq_zero_of_not_mem_support hresult]
                simp
          _ = (∑' result, Pr[= result | head]) *
                (resource initialState + indicator) :=
              ENNReal.tsum_mul_right
          _ ≤ 1 * (resource initialState + indicator) := by
              gcongr
              exact tsum_probOutput_le_one
          _ = resource initialState + indicator := one_mul _
      calc
        (∑' result, Pr[= result | head] *
            ∑' finalResult,
              Pr[= finalResult |
                (simulateQ implementation (next result.1)).run result.2] *
                resource finalResult.2) ≤
          ∑' result, Pr[= result | head] *
            (resource result.2 +
              expectedSimulatedQueryCount implementation predicate
                (next result.1) result.2) := by
            apply ENNReal.tsum_le_tsum
            intro result
            exact mul_le_mul_right (ih result.1 result.2) _
        _ = (∑' result, Pr[= result | head] * resource result.2) +
            ∑' result, Pr[= result | head] *
              expectedSimulatedQueryCount implementation predicate
                (next result.1) result.2 := by
            simp_rw [mul_add]
            rw [ENNReal.tsum_add]
        _ ≤ (resource initialState + indicator) +
            ∑' result, Pr[= result | head] *
              expectedSimulatedQueryCount implementation predicate
                (next result.1) result.2 := add_le_add hhead le_rfl
        _ = resource initialState +
            (indicator +
              ∑' result, Pr[= result | head] *
                expectedSimulatedQueryCount implementation predicate
                  (next result.1) result.2) := by ac_rfl

/-- Expected simulated query counts add exactly for disjoint source predicates. -/
theorem expectedSimulatedQueryCount_or_of_disjoint
    {ι : Type} {spec : OracleSpec ι} {α state : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (left right : spec.Domain → Prop) [DecidablePred left] [DecidablePred right]
    (hdisjoint : ∀ input, ¬(left input ∧ right input))
    (computation : OracleComp spec α) (initialState : state) :
    expectedSimulatedQueryCount implementation
        (fun input => left input ∨ right input) computation initialState =
      expectedSimulatedQueryCount implementation left computation initialState +
        expectedSimulatedQueryCount implementation right computation initialState := by
  induction computation using OracleComp.recOn generalizing initialState with
  | pure value =>
      change expectedSimulatedQueryCount implementation
          (fun input => left input ∨ right input)
          (pure value : OracleComp spec α) initialState =
        expectedSimulatedQueryCount implementation left
            (pure value : OracleComp spec α) initialState +
          expectedSimulatedQueryCount implementation right
            (pure value : OracleComp spec α) initialState
      simp
  | queryBind input next ih =>
      change (if left input ∨ right input then 1 else 0) +
          ∑' result, Pr[= result | (implementation input).run initialState] *
            expectedSimulatedQueryCount implementation
              (fun input => left input ∨ right input) (next result.1) result.2 =
        ((if left input then 1 else 0) +
          ∑' result, Pr[= result | (implementation input).run initialState] *
            expectedSimulatedQueryCount implementation left
              (next result.1) result.2) +
        ((if right input then 1 else 0) +
          ∑' result, Pr[= result | (implementation input).run initialState] *
            expectedSimulatedQueryCount implementation right
              (next result.1) result.2)
      simp_rw [ih, mul_add]
      rw [ENNReal.tsum_add]
      have hindicator :
          (if left input ∨ right input then (1 : ENNReal) else 0) =
            (if left input then 1 else 0) + (if right input then 1 else 0) := by
        by_cases hleft : left input <;> by_cases hright : right input
        · exact (hdisjoint input ⟨hleft, hright⟩).elim
        · simp [hleft, hright]
        · simp [hleft, hright]
        · simp [hleft, hright]
      rw [hindicator]
      ac_rfl

end XmssSecurity
