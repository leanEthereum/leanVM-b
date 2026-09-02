import SphincsSecurity.Proof.OtsProbeResolvedPrivateRecursive
import SphincsSecurity.Proof.MarginalCoupling

/-!
# Retained private-position commutation

The ordinary commutation lemmas expose only the common state after both resolvers have run. This
module retains the state immediately before the delayed target resolution as well. That retained
state is the left side needed by the event-specific lazy/eager coupling.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def resolveResolverThenPositionRetained
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext) :
    ProbComp (Option (DeferredResolution × Option RevealedResolution)) := do
  let resolved ← resolver context
  match resolved with
  | none => pure none
  | some resolved => do
      let targetResolved ← resolveDeferredPositionValue target resolved.toDeferredContext
      pure (some (resolved, targetResolved.map fun targetResolved =>
        ⟨targetResolved.toDeferredContext, resolved.output⟩))

def retainedPositionResolutionBefore :
    Option (DeferredResolution × Option RevealedResolution) → Option DeferredResolution :=
  Option.map Prod.fst

def retainedPositionResolutionAfter :
    Option (DeferredResolution × Option RevealedResolution) → Option RevealedResolution
  | none => none
  | some pair => pair.2

def RetainedPositionResolutionRel
    (target : Position) : Option DeferredResolution → Option RevealedResolution → Prop
  | none, after => after = none
  | some before, after =>
      ∃ targetResolved,
        targetResolved ∈ support
          (resolveDeferredPositionValue target before.toDeferredContext) ∧
        after = targetResolved.map fun targetResolved =>
          ⟨targetResolved.toDeferredContext, before.output⟩

theorem evalDist_map_before_resolveResolverThenPositionRetained
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext) :
    evalDist (retainedPositionResolutionBefore <$>
        resolveResolverThenPositionRetained target resolver context) =
      evalDist (resolver context) := by
  unfold resolveResolverThenPositionRetained retainedPositionResolutionBefore
  simp only [map_eq_bind_pure_comp, bind_assoc]
  calc
    _ = evalDist (resolver context >>= fun resolved => pure resolved) := by
      apply evalDist_bind_congr
      intro resolved _hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          calc
            _ = evalDist (resolveDeferredPositionValue target resolved.toDeferredContext >>=
                fun _ => pure (some resolved)) := by
                  simp only
                  rw [bind_assoc]
                  apply evalDist_bind_congr
                  intro targetResolved _htargetResolved
                  cases targetResolved <;> rfl
            _ = evalDist (pure (some resolved) : ProbComp (Option DeferredResolution)) :=
              OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                (resolveDeferredPositionValue target resolved.toDeferredContext)
                (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
                (pure (some resolved))
    _ = _ := by rw [bind_pure]

theorem map_snd_resolveResolverThenPositionRetained
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext) :
    retainedPositionResolutionAfter <$>
        resolveResolverThenPositionRetained target resolver context =
      resolveResolverThenPosition target resolver context := by
  unfold resolveResolverThenPositionRetained resolveResolverThenPosition
    retainedPositionResolutionAfter
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro resolved
  cases resolved with
  | none => rfl
  | some resolved =>
      simp only
      rw [bind_assoc]
      apply bind_congr
      intro targetResolved
      cases targetResolved <;> rfl

theorem retainedPositionResolutionRel_of_mem
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext)
    (pair : Option (DeferredResolution × Option RevealedResolution))
    (hpair : pair ∈ support
      (resolveResolverThenPositionRetained target resolver context)) :
    RetainedPositionResolutionRel target (retainedPositionResolutionBefore pair)
      (retainedPositionResolutionAfter pair) := by
  unfold resolveResolverThenPositionRetained at hpair
  rw [mem_support_bind_iff] at hpair
  obtain ⟨resolved, hresolved, hpair⟩ := hpair
  cases resolved with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hpair
      subst pair
      rfl
  | some resolved =>
      rw [mem_support_bind_iff] at hpair
      obtain ⟨targetResolved, htargetResolved, hpair⟩ := hpair
      simp only [support_pure, Set.mem_singleton_iff] at hpair
      subst pair
      exact ⟨targetResolved, htargetResolved, rfl⟩

theorem relTriple_retainedPositionResolution
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext) :
    RelTriple
      (retainedPositionResolutionBefore <$>
        resolveResolverThenPositionRetained target resolver context)
      (retainedPositionResolutionAfter <$>
        resolveResolverThenPositionRetained target resolver context)
      (RetainedPositionResolutionRel target) := by
  let shared := resolveResolverThenPositionRetained target resolver context
  have hbase :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
      (relTriple_refl shared) (fun pair => pair ∈ support shared) (fun _ hpair => hpair)
  have hsemantic : RelTriple shared shared
      (fun left right => RetainedPositionResolutionRel target
        (retainedPositionResolutionBefore left) (retainedPositionResolutionAfter right)) := by
    apply relTriple_post_mono hbase
    intro left right hrelation
    obtain ⟨heq, hleft⟩ := hrelation
    subst right
    exact retainedPositionResolutionRel_of_mem target resolver context left hleft
  exact relTriple_map hsemantic

theorem relTriple_resolverThenPosition_resolvePositionThenResolver_retained
    (target : Position) (resolver : PrivateResolver) (context : DeferredContext)
    (hcommutes : PositionResolutionCommutes target resolver context) :
    RelTriple
      (resolver context)
      (resolvePositionThenResolver target resolver context)
      (RetainedPositionResolutionRel target) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_map_before_resolveResolverThenPositionRetained target resolver context).symm
  apply relTriple_of_evalDist_eq_right
    (ob := retainedPositionResolutionAfter <$>
      resolveResolverThenPositionRetained target resolver context)
    (ob' := resolvePositionThenResolver target resolver context)
  · calc
      evalDist (retainedPositionResolutionAfter <$>
          resolveResolverThenPositionRetained target resolver context) =
          evalDist (resolveResolverThenPosition target resolver context) := by
            rw [map_snd_resolveResolverThenPositionRetained]
      _ = evalDist (resolvePositionThenResolver target resolver context) := hcommutes.symm
  · exact relTriple_retainedPositionResolution target resolver context

end SphincsSecurity.Concrete.OtsProbeSimulation
