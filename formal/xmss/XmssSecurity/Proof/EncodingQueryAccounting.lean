import XmssSecurity.Proof.EncodingOracleSimulation
import XmssSecurity.Proof.EncodingAddressQueryBound
import VCVio.OracleComp.QueryTracking.SubSpec

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000

theorem isQueryBoundP_lifted_query_bind_iff
    {sourceIndex targetIndex : Type}
    {sourceSpec : OracleSpec sourceIndex} {targetSpec : OracleSpec targetIndex}
    [inclusion : sourceSpec ⊂ₒ targetSpec]
    (input : sourceSpec.Domain)
    (next : sourceSpec.Range input → OracleComp targetSpec α)
    (predicate : targetSpec.Domain → Prop) [DecidablePred predicate]
    (fuel : Nat) :
    ((OracleComp.liftComp
        (liftM (sourceSpec.query input) :
          OracleComp sourceSpec (sourceSpec.Range input)) targetSpec >>= next)
      |>.IsQueryBoundP predicate fuel) ↔
      (¬ predicate (inclusion.onQuery input) ∨ 0 < fuel) ∧
        ∀ response, (next (inclusion.onResponse input response)).IsQueryBoundP
          predicate (if predicate (inclusion.onQuery input) then fuel - 1 else fuel) := by
  rw [show
      OracleComp.liftComp
          (liftM (sourceSpec.query input) :
            OracleComp sourceSpec (sourceSpec.Range input)) targetSpec =
        liftM (targetSpec.query (inclusion.onQuery input)) >>= fun response =>
          pure (inclusion.onResponse input response) by
    rw [OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query]
    change
      ((liftM (sourceSpec.query input) :
        OracleQuery targetSpec (sourceSpec.Range input)) :
          OracleComp targetSpec (sourceSpec.Range input)) = _
    rw [show
        (liftM (sourceSpec.query input) :
          OracleQuery targetSpec (sourceSpec.Range input)) =
            ⟨inclusion.onQuery input, inclusion.onResponse input⟩
      from inclusion.liftM_eq_lift _]
    rfl]
  rw [bind_assoc, OracleComp.isQueryBoundP_query_bind_iff]
  simp only [pure_bind]

theorem isQueryBoundP_bind_congr_right
    {index : Type} {spec : OracleSpec index} {α β : Type}
    (head : OracleComp spec α)
    (leftNext rightNext : α → OracleComp spec β)
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP predicate fuel ↔
        (rightNext result).IsQueryBoundP predicate fuel)
    (fuel : Nat) :
    (head >>= leftNext).IsQueryBoundP predicate fuel ↔
      (head >>= rightNext).IsQueryBoundP predicate fuel := by
  induction head using OracleComp.inductionOn generalizing fuel with
  | pure result =>
      simpa only [pure_bind] using hnext result fuel
  | query_bind input next ih =>
      rw [bind_assoc, bind_assoc,
        OracleComp.isQueryBoundP_query_bind_iff,
        OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · rintro ⟨hpositive, hrest⟩
        exact ⟨hpositive, fun response =>
          (ih response (if predicate input then fuel - 1 else fuel)).mp
            (hrest response)⟩
      · rintro ⟨hpositive, hrest⟩
        exact ⟨hpositive, fun response =>
          (ih response (if predicate input then fuel - 1 else fuel)).mpr
            (hrest response)⟩

theorem OracleComp.IsQueryBoundP.bind_right_of_mem_support
    {index : Type} {spec : OracleSpec index} {α β : Type}
    {predicate : spec.Domain → Prop} [DecidablePred predicate]
    {head : OracleComp spec α} {next : α → OracleComp spec β}
    {fuel : Nat}
    (hbound : (head >>= next).IsQueryBoundP predicate fuel)
    (result : α) (hresult : result ∈ support head) :
    (next result).IsQueryBoundP predicate fuel := by
  induction head using OracleComp.inductionOn generalizing fuel result with
  | pure value =>
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simpa only [pure_bind] using hbound
  | query_bind input rest ih =>
      rw [bind_assoc, OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [mem_support_bind_iff] at hresult
      obtain ⟨response, _hquery, hrest⟩ := hresult
      exact (ih response (hbound.2 response) result hrest).mono (by
        split <;> omega)

theorem splitRandomOracle_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec) (fuel : Nat) :
    ((splitRandomOracle parameter leftKind input).run cache).IsQueryBoundP
        (· matches .inr _) fuel ↔
      ((splitRandomOracle parameter rightKind input).run cache).IsQueryBoundP
        (· matches .inr _) fuel := by
  unfold splitRandomOracle
  cases hcache : cache input with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hcache,
        QueryImpl.withCaching_run_some _ hcache]
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache,
        QueryImpl.withCaching_run_none _ hcache,
        OracleComp.isQueryBoundP_map_iff,
        OracleComp.isQueryBoundP_map_iff]
      unfold freshEncodingSampleImpl encodingSampleAddress
      cases hepoch : encodingInputEpoch? parameter input with
      | none => simp only [encodingSampleAddressFromEpoch]
      | some epoch =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [OracleComp.liftComp_query, OracleComp.liftComp_query,
            OracleComp.isQueryBoundP_map_iff,
            OracleComp.isQueryBoundP_map_iff]
          cases leftKind <;> cases rightKind <;> rfl

theorem splitRandomOracle_bind_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (input : HashInput) (cache : QueryCache HashSpec)
    (leftNext rightNext : HashOutput × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld α)
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP (· matches .inr _) fuel ↔
        (rightNext result).IsQueryBoundP (· matches .inr _) fuel)
    (fuel : Nat) :
    (((splitRandomOracle parameter leftKind input).run cache >>= leftNext)
        |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((splitRandomOracle parameter rightKind input).run cache >>= rightNext)
        |>.IsQueryBoundP (· matches .inr _) fuel) := by
  unfold splitRandomOracle
  cases hcache : cache input with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hcache,
        QueryImpl.withCaching_run_some _ hcache]
      simp only [pure_bind]
      exact hnext (output, cache) fuel
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache,
        QueryImpl.withCaching_run_none _ hcache]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      unfold freshEncodingSampleImpl encodingSampleAddress
      cases hepoch : encodingInputEpoch? parameter input with
      | none =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [isQueryBoundP_lifted_query_bind_iff,
            isQueryBoundP_lifted_query_bind_iff]
          constructor
          · rintro ⟨hpositive, hrest⟩
            exact ⟨hpositive, fun output =>
              (hnext (output, cache.cacheQuery input output) (fuel - 1)).mp
                (hrest output)⟩
          · rintro ⟨hpositive, hrest⟩
            exact ⟨hpositive, fun output =>
              (hnext (output, cache.cacheQuery input output) (fuel - 1)).mpr
                (hrest output)⟩
      | some epoch =>
          simp only [encodingSampleAddressFromEpoch]
          unfold encodingSampleQuery
          rw [isQueryBoundP_lifted_query_bind_iff,
            isQueryBoundP_lifted_query_bind_iff]
          constructor
          · rintro ⟨hpositive, hrest⟩
            exact ⟨hpositive, fun output =>
              (hnext (output, cache.cacheQuery input output) (fuel - 1)).mp
                (hrest output)⟩
          · rintro ⟨hpositive, hrest⟩
            exact ⟨hpositive, fun output =>
              (hnext (output, cache.cacheQuery input output) (fuel - 1)).mpr
                (hrest output)⟩

theorem splitRandomOracle_simulateQ_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (computation : OracleComp HashSpec α) (cache : QueryCache HashSpec)
    (fuel : Nat) :
    (((simulateQ (splitRandomOracle parameter leftKind) computation).run cache)
        |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((simulateQ (splitRandomOracle parameter rightKind) computation).run cache)
        |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind,
        simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      exact splitRandomOracle_bind_kind_isQueryBoundP_iff parameter leftKind
        rightKind input cache
          (fun result =>
            (simulateQ (splitRandomOracle parameter leftKind) (next result.1)).run
              result.2)
          (fun result =>
            (simulateQ (splitRandomOracle parameter rightKind) (next result.1)).run
              result.2)
          (fun result remaining => ih result.1 result.2 remaining) fuel

theorem splitXmssRom_bind_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (leftNext rightNext : OracleWorld.Range input × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld α)
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP (· matches .inr _) fuel ↔
        (rightNext result).IsQueryBoundP (· matches .inr _) fuel)
    (fuel : Nat) :
    (((splitXmssRomImpl parameter leftKind input).run cache >>= leftNext)
        |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((splitXmssRomImpl parameter rightKind input).run cache >>= rightNext)
        |>.IsQueryBoundP (· matches .inr _) fuel) := by
  cases input with
  | inl uniformInput =>
      simp only [splitXmssRomImpl, QueryImpl.add_apply_inl]
      exact isQueryBoundP_bind_congr_right
        ((splitUniformOracle uniformInput).run cache) leftNext rightNext
        (· matches .inr _) hnext fuel
  | inr hashInput =>
      simp only [splitXmssRomImpl, QueryImpl.add_apply_inr]
      exact splitRandomOracle_bind_kind_isQueryBoundP_iff parameter leftKind
        rightKind hashInput cache leftNext rightNext hnext fuel

theorem splitXmssRom_simulateQ_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (fuel : Nat) :
    (((simulateQ (splitXmssRomImpl parameter leftKind) computation).run cache)
        |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      (((simulateQ (splitXmssRomImpl parameter rightKind) computation).run cache)
        |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind,
        simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      exact splitXmssRom_bind_kind_isQueryBoundP_iff parameter leftKind
        rightKind input cache
          (fun result =>
            (simulateQ (splitXmssRomImpl parameter leftKind) (next result.1)).run
              result.2)
          (fun result =>
            (simulateQ (splitXmssRomImpl parameter rightKind) (next result.1)).run
              result.2)
          (fun result remaining => ih result.1 result.2 remaining) fuel

theorem splitXmssRom_simulateQ_bind_kind_isQueryBoundP_iff
    (parameter : PublicParameter) (leftKind rightKind : EncodingSampleKind)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (leftNext rightNext : α × QueryCache HashSpec →
      OracleComp EncodingSamplingWorld β)
    (hnext : ∀ result fuel,
      (leftNext result).IsQueryBoundP (· matches .inr _) fuel ↔
        (rightNext result).IsQueryBoundP (· matches .inr _) fuel)
    (fuel : Nat) :
    ((((simulateQ (splitXmssRomImpl parameter leftKind) computation).run cache) >>=
        leftNext) |>.IsQueryBoundP (· matches .inr _) fuel) ↔
      ((((simulateQ (splitXmssRomImpl parameter rightKind) computation).run cache) >>=
        rightNext) |>.IsQueryBoundP (· matches .inr _) fuel) := by
  induction computation using OracleComp.inductionOn generalizing cache fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hnext (value, cache) fuel
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, bind_assoc,
        simulateQ_query_bind, StateT.run_bind, bind_assoc]
      simp only [OracleQuery.input_query, monadLift_self]
      exact splitXmssRom_bind_kind_isQueryBoundP_iff parameter leftKind
        rightKind input cache
          (fun result =>
            (simulateQ (splitXmssRomImpl parameter leftKind) (next result.1)).run
              result.2 >>= leftNext)
          (fun result =>
            (simulateQ (splitXmssRomImpl parameter rightKind) (next result.1)).run
              result.2 >>= rightNext)
          (fun result remaining =>
            ih result.1 result.2 remaining) fuel


end XmssSecurity

