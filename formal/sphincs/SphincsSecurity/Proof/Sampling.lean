import SphincsSecurity.Proof.Guess
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Marginals of the sampled secret tables

The statement samples whole finite function tables uniformly. Every fixed coordinate is therefore
a uniform digest, without expanding the sampler's function-type `Fintype` instance.
-/

namespace SphincsSecurity

open OracleComp ENNReal

noncomputable local instance {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R

theorem evalDist_uniform_function_bind_cell_extract {D R β : Type}
    [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    (index : D) (cont : (D → R) → R → ProbComp β) :
    𝒟[do
      let table ← ($ᵗ (D → R) : ProbComp (D → R))
      cont table (table index)] =
    𝒟[do
      let value ← ($ᵗ R : ProbComp R)
      let table ← ($ᵗ (D → R) : ProbComp (D → R))
      cont (Function.update table index value) value] := by
  classical
  have hleft :
      (do
        let table ← ($ᵗ (D → R) : ProbComp (D → R))
        cont table (table index)) =
      ((do
          let table ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (table, table index)) >>= fun pair => cont pair.1 pair.2) := by
    simp
  have hright :
      (do
        let value ← ($ᵗ R : ProbComp R)
        let table ← ($ᵗ (D → R) : ProbComp (D → R))
        cont (Function.update table index value) value) =
      ((do
          let value ← ($ᵗ R : ProbComp R)
          let table ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (Function.update table index value, value)) >>=
        fun pair => cont pair.1 pair.2) := by
    simp
  rw [hleft, hright]
  have hpureEq : ∀ (table : D → R) (value : R),
      (Function.update table index value, value) =
        ((fun table' : D → R => (table', table' index))
          (Function.update table index value)) := fun _ _ => by simp
  have hcore :
      𝒟[do
        let value ← ($ᵗ R : ProbComp R)
        let table ← ($ᵗ (D → R) : ProbComp (D → R))
        pure (Function.update table index value, value)] =
      𝒟[do
        let table ← ($ᵗ (D → R) : ProbComp (D → R))
        pure (table, table index)] := by
    have hrw :
        (do
          let value ← ($ᵗ R : ProbComp R)
          let table ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (Function.update table index value, value)) =
        (do
          let value ← ($ᵗ R : ProbComp R)
          let table ← ($ᵗ (D → R) : ProbComp (D → R))
          pure ((fun table' : D → R => (table', table' index))
            (Function.update table index value))) :=
      bind_congr fun value => bind_congr fun table => by rw [hpureEq table value]
    rw [hrw]
    exact OracleComp.evalDist_uniformSample_bind_update_map (R := R) index
      (fun table' => (table', table' index))
  refine evalDist_ext fun output => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun pair => ?_
  rw [show Pr[= pair | (do
        let table ← ($ᵗ (D → R) : ProbComp (D → R))
        pure (table, table index))] =
      Pr[= pair | (do
        let value ← ($ᵗ R : ProbComp R)
        let table ← ($ᵗ (D → R) : ProbComp (D → R))
        pure (Function.update table index value, value))] from
    probOutput_congr rfl hcore.symm]

theorem evalDist_uniform_function_bind_cell_extract3 {I J K R β : Type}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (i : I) (j : J) (k : K) (cont : (I → J → K → R) → R → ProbComp β) :
    𝒟[do
      let table ← ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))
      cont table (table i j k)] =
    𝒟[do
      let value ← ($ᵗ R : ProbComp R)
      let rowK ← ($ᵗ (K → R) : ProbComp (K → R))
      let rowJ ← ($ᵗ (J → K → R) : ProbComp (J → K → R))
      let table ← ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))
      cont (Function.update table i
        (Function.update rowJ j (Function.update rowK k value))) value] := by
  calc
    𝒟[do
      let table ← ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))
      cont table (table i j k)] =
        𝒟[do
          let rowJ ← ($ᵗ (J → K → R) : ProbComp (J → K → R))
          let table ← ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))
          cont (Function.update table i rowJ) (rowJ j k)] :=
      evalDist_uniform_function_bind_cell_extract i
        (fun table rowJ => cont table (rowJ j k))
    _ = 𝒟[do
          let rowK ← ($ᵗ (K → R) : ProbComp (K → R))
          let rowJ ← ($ᵗ (J → K → R) : ProbComp (J → K → R))
          let table ← ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))
          cont (Function.update table i (Function.update rowJ j rowK)) (rowK k)] :=
      evalDist_uniform_function_bind_cell_extract j (fun rowJ rowK => do
        let table ← ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))
        cont (Function.update table i rowJ) (rowK k))
    _ = 𝒟[do
          let value ← ($ᵗ R : ProbComp R)
          let rowK ← ($ᵗ (K → R) : ProbComp (K → R))
          let rowJ ← ($ᵗ (J → K → R) : ProbComp (J → K → R))
          let table ← ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))
          cont (Function.update table i
            (Function.update rowJ j (Function.update rowK k value))) value] :=
      evalDist_uniform_function_bind_cell_extract k (fun rowK value => do
        let rowJ ← ($ᵗ (J → K → R) : ProbComp (J → K → R))
        let table ← ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))
        cont (Function.update table i (Function.update rowJ j rowK)) value)

theorem evalDist_uniform_function_bind_cell_extract4 {I J K L R β : Type}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (i : I) (j : J) (k : K) (l : L)
    (cont : (I → J → K → L → R) → R → ProbComp β) :
    𝒟[do
      let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
      cont table (table i j k l)] =
    𝒟[do
      let value ← ($ᵗ R : ProbComp R)
      let rowL ← ($ᵗ (L → R) : ProbComp (L → R))
      let rowK ← ($ᵗ (K → L → R) : ProbComp (K → L → R))
      let rowJ ← ($ᵗ (J → K → L → R) : ProbComp (J → K → L → R))
      let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
      cont (Function.update table i (Function.update rowJ j
        (Function.update rowK k (Function.update rowL l value)))) value] := by
  calc
    𝒟[do
      let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
      cont table (table i j k l)] =
        𝒟[do
          let rowJ ← ($ᵗ (J → K → L → R) : ProbComp (J → K → L → R))
          let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
          cont (Function.update table i rowJ) (rowJ j k l)] :=
      evalDist_uniform_function_bind_cell_extract i
        (fun table rowJ => cont table (rowJ j k l))
    _ = 𝒟[do
          let rowK ← ($ᵗ (K → L → R) : ProbComp (K → L → R))
          let rowJ ← ($ᵗ (J → K → L → R) : ProbComp (J → K → L → R))
          let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
          cont (Function.update table i (Function.update rowJ j rowK)) (rowK k l)] :=
      evalDist_uniform_function_bind_cell_extract j (fun rowJ rowK => do
        let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
        cont (Function.update table i rowJ) (rowK k l))
    _ = 𝒟[do
          let rowL ← ($ᵗ (L → R) : ProbComp (L → R))
          let rowK ← ($ᵗ (K → L → R) : ProbComp (K → L → R))
          let rowJ ← ($ᵗ (J → K → L → R) : ProbComp (J → K → L → R))
          let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
          cont (Function.update table i
            (Function.update rowJ j (Function.update rowK k rowL))) (rowL l)] :=
      evalDist_uniform_function_bind_cell_extract k (fun rowK rowL => do
        let rowJ ← ($ᵗ (J → K → L → R) : ProbComp (J → K → L → R))
        let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
        cont (Function.update table i (Function.update rowJ j rowK)) (rowL l))
    _ = 𝒟[do
          let value ← ($ᵗ R : ProbComp R)
          let rowL ← ($ᵗ (L → R) : ProbComp (L → R))
          let rowK ← ($ᵗ (K → L → R) : ProbComp (K → L → R))
          let rowJ ← ($ᵗ (J → K → L → R) : ProbComp (J → K → L → R))
          let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
          cont (Function.update table i (Function.update rowJ j
            (Function.update rowK k (Function.update rowL l value)))) value] :=
      evalDist_uniform_function_bind_cell_extract l (fun rowL value => do
        let rowK ← ($ᵗ (K → L → R) : ProbComp (K → L → R))
        let rowJ ← ($ᵗ (J → K → L → R) : ProbComp (J → K → L → R))
        let table ← ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))
        cont (Function.update table i
          (Function.update rowJ j (Function.update rowK k rowL))) value)

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

theorem evalDist_uniform_function_eval3 {I J K R : Type}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype R] [DecidableEq R] [Nonempty R] (i : I) (j : J) (k : K) :
    𝒟[(fun table : I → J → K → R => table i j k) <$>
        ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))] =
      𝒟[($ᵗ R : ProbComp R)] := by
  have h1 := evalDist_uniform_function_eval (R := J → K → R) i
  have h2 := evalDist_uniform_function_eval (R := K → R) j
  have h3 := evalDist_uniform_function_eval (R := R) k
  have htail : 𝒟[(fun tail : K → R => tail k) <$>
      ((fun slice : J → K → R => slice j) <$> ($ᵗ (J → K → R) : ProbComp (J → K → R)))] =
      𝒟[($ᵗ R : ProbComp R)] := by
    rw [evalDist_map, h2, ← evalDist_map]
    exact h3
  have htail' : 𝒟[(fun slice : J → K → R => slice j k) <$>
      ($ᵗ (J → K → R) : ProbComp (J → K → R))] = 𝒟[($ᵗ R : ProbComp R)] := by
    simpa [map_eq_bind_pure_comp, bind_assoc] using htail
  have hnested : 𝒟[(fun slice : J → K → R => slice j k) <$>
      ((fun table : I → J → K → R => table i) <$>
        ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R)))] = 𝒟[($ᵗ R : ProbComp R)] := by
    rw [evalDist_map, h1, ← evalDist_map]
    exact htail'
  simpa [map_eq_bind_pure_comp, bind_assoc] using hnested

theorem uniform_function_coordinate3_probability {I J K R : Type}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (i : I) (j : J) (k : K) (target : R) :
    Pr[fun table : I → J → K → R => table i j k = target |
        ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))] =
      ((Fintype.card R : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[fun table : I → J → K → R => table i j k = target |
        ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))] =
      Pr[fun value : R => value = target |
        (fun table : I → J → K → R => table i j k) <$>
          ($ᵗ (I → J → K → R) : ProbComp (I → J → K → R))] := by
        rw [probEvent_map]
        rfl
    _ = Pr[fun value : R => value = target | ($ᵗ R : ProbComp R)] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_uniform_function_eval3 i j k)
    _ = ((Fintype.card R : Nat) : ℝ≥0∞)⁻¹ := by
      simp only [probEvent_eq_eq_probOutput, probOutput_uniformSample]

theorem evalDist_uniform_function_eval4 {I J K L R : Type}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R] (i : I) (j : J) (k : K) (l : L) :
    𝒟[(fun table : I → J → K → L → R => table i j k l) <$>
        ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))] =
      𝒟[($ᵗ R : ProbComp R)] := by
  have h1 := evalDist_uniform_function_eval (R := J → K → L → R) i
  have h2 := evalDist_uniform_function_eval3 (I := J) (J := K) (K := L) (R := R) j k l
  have hnested : 𝒟[(fun slice : J → K → L → R => slice j k l) <$>
      ((fun table : I → J → K → L → R => table i) <$>
        ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R)))] = 𝒟[($ᵗ R : ProbComp R)] := by
    rw [evalDist_map, h1, ← evalDist_map]
    exact h2
  simpa [map_eq_bind_pure_comp, bind_assoc] using hnested

theorem uniform_function_coordinate4_probability {I J K L R : Type}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (i : I) (j : J) (k : K) (l : L) (target : R) :
    Pr[fun table : I → J → K → L → R => table i j k l = target |
        ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))] =
      ((Fintype.card R : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[fun table : I → J → K → L → R => table i j k l = target |
        ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))] =
      Pr[fun value : R => value = target |
        (fun table : I → J → K → L → R => table i j k l) <$>
          ($ᵗ (I → J → K → L → R) : ProbComp (I → J → K → L → R))] := by
        rw [probEvent_map]
        rfl
    _ = Pr[fun value : R => value = target | ($ᵗ R : ProbComp R)] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_uniform_function_eval4 i j k l)
    _ = ((Fintype.card R : Nat) : ℝ≥0∞)⁻¹ := by
      simp only [probEvent_eq_eq_probOutput, probOutput_uniformSample]

end SphincsSecurity
