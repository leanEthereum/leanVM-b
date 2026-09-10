import SphincsSecurity.Proof.Prelude

/-!
# Marginals of the sampled secret tables

The statement samples whole finite function tables uniformly. Every fixed coordinate is therefore
a uniform digest, without expanding the sampler's function-type `Fintype` instance.
-/

namespace SphincsSecurity

open OracleComp ENNReal

noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R

theorem evalDist_uniform_function_eval {I R : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype R] [DecidableEq R] [Nonempty R] (index : I) :
    𝒟[(fun table : I → R => table index) <$> ($ᵗ (I → R) : ProbComp (I → R))] =
      𝒟[($ᵗ R : ProbComp R)] := by
  let embed : Unit → I := fun _ => index
  have hembed : Function.Injective embed := by
    intro left right _
    cases left
    cases right
    rfl
  let evaluate : (Unit → R) → R := fun table => table ()
  have hevaluate : Function.Bijective evaluate := by
    constructor
    · intro left right heq
      funext input
      cases input
      exact heq
    · intro value
      exact ⟨fun _ => value, rfl⟩
  have hrestrict :
      𝒟[(fun table : I → R => table ∘ embed) <$> ($ᵗ (I → R) : ProbComp (I → R))] =
        𝒟[($ᵗ (Unit → R) : ProbComp (Unit → R))] := by
    simpa only [bind_pure_comp] using
      evalDist_uniformSample_map_comp_injective (R := R) hembed
  have hmarginal : 𝒟[evaluate <$> ((fun table : I → R => table ∘ embed) <$>
      ($ᵗ (I → R) : ProbComp (I → R)))] = 𝒟[($ᵗ R : ProbComp R)] := by
    rw [evalDist_map, hrestrict, ← evalDist_map]
    exact evalDist_map_bijective_uniform_cross
      (α := Unit → R) (β := R) evaluate hevaluate
  simpa [map_eq_bind_pure_comp, bind_assoc, evaluate, embed] using hmarginal

theorem uniform_function_coordinate_probability {I R : Type}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype R] [DecidableEq R] [Nonempty R]
    (index : I) (target : R) :
    Pr[fun table : I → R => table index = target | ($ᵗ (I → R) : ProbComp (I → R))] =
      ((Fintype.card R : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[fun table : I → R => table index = target | ($ᵗ (I → R) : ProbComp (I → R))] =
        Pr[fun value : R => value = target |
          (fun table : I → R => table index) <$> ($ᵗ (I → R) : ProbComp (I → R))] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun value : R => value = target | ($ᵗ R : ProbComp R)] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_uniform_function_eval index)
    _ = ((Fintype.card R : Nat) : ℝ≥0∞)⁻¹ := by
      simp only [probEvent_eq_eq_probOutput, probOutput_uniformSample]

end SphincsSecurity
