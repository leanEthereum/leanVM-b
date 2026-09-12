import SphincsSecurity.Proof.Base.UniformTableObservation
namespace SphincsSecurity.Concrete.UniformTableObservation

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false

theorem lazyRun_neverFail {Coordinate Value AuxIndex Result : Type} [DecidableEq Coordinate]
    {auxSpec : OracleSpec AuxIndex} (auxiliary : QueryImpl auxSpec SPMF)
    (haux : ∀ input, NeverFail (auxiliary input))
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result)
    (allowed : Coordinate → Finset Value) (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    NeverFail (lazyRun auxiliary computation allowed) := by
  induction computation using OracleComp.inductionOn generalizing allowed with
  | pure value => rw [lazyRun_pure]; infer_instance
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left, neverFail_bind_iff]
          exact ⟨haux input, fun answer _ => ih answer allowed ha⟩
      | inr coordinate =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left, neverFail_bind_iff]
          constructor
          · rw [cell, dif_pos (ha coordinate)]
            exact ⟨probFailure_of_liftM_PMF _⟩
          · intro answer _
            exact ih answer _ (discloseTableValue_nonempty allowed ha coordinate answer)

end SphincsSecurity.Concrete.UniformTableObservation
