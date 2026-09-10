import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbePrivateValueProbeCut
import SphincsSecurity.Proof.OtsProbeStartHistorySupport

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem known_coordinate_of_mem_runResolvedFromTable
    (target : Coordinate) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation))
    (hknown : context.state.values target ≠ none) : result.context.state.values target ≠ none := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact hknown
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail hknown
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel htail hknown
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hresult hknown
      | probe coordinate digest =>
          cases fuel with
          | zero => simp [runResolvedFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runResolvedFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining (by simpa only [hrevealed, ↓reduceIte] using hresult) hknown
              · exact ih () { context with state := context.state.addPending coordinate digest } remaining
                  (by simpa only [hrevealed, ↓reduceIte] using hresult) hknown
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult hknown
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hresult hknown
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate <;> rw [mem_support_bind_iff] at hresult
          all_goals
            obtain ⟨option, _hresolve, htail⟩ := hresult
            cases option with
            | none => simp at htail
            | some resolved =>
                apply ih resolved.output _ fuel htail
                simp only [LazyRevealProbe.State.materialize, Function.update_apply]
                split_ifs <;> simp_all

def PrivateTargetInactive (target : Position) (context : DeferredContext) : Prop :=
  context.state.values (.position target) ≠ none ∨ .position target ∈ context.state.revealed

theorem PrivateTargetInactive.of_mem_runResolved
    {target : Position} {context : DeferredContext} (hinactive : PrivateTargetInactive target context)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    PrivateTargetInactive target result.context := by
  rcases hinactive with hknown | hpublic
  · exact Or.inl (known_coordinate_of_mem_runResolvedFromTable _ computation context fuel table result hresult hknown)
  · exact Or.inr ((revealed_subset_of_mem_runResolvedFromTable computation context fuel table result hresult) hpublic)

theorem privateTargetInactive_of_disclosure
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hdisclose : IsPrivatePositionDisclosure target input)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next))) :
    PrivateTargetInactive target result.context := by
  cases input <;> simp only [IsPrivatePositionDisclosure] at hdisclose
  case publish coordinate =>
    subst coordinate
    rw [runResolvedFromTable_publish_query_bind] at hresult
    apply PrivateTargetInactive.of_mem_runResolved (context := { context with state := context.state.publish (.position target) })
      (Or.inr (by simp [LazyRevealProbe.State.publish])) _ fuel table result hresult
  case reveal coordinate =>
    subst coordinate
    rw [runResolvedFromTable_reveal_query_bind, mem_support_bind_iff] at hresult
    obtain ⟨resolved, _, htail⟩ := hresult
    cases resolved with
    | none => simp at htail
    | some resolved =>
        apply PrivateTargetInactive.of_mem_runResolved (context :=
          { state := context.state.materialize (.position target) resolved.output, values := resolved.values })
          (Or.inl (by simp [LazyRevealProbe.State.materialize])) _ fuel table result htail

end SphincsSecurity.Concrete.OtsProbeSimulation
