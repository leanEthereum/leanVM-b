import SphincsSecurity.Proof.FiniteHashWorld

namespace SphincsSecurity.Concrete.FiniteGraphSampling

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false

variable {Node Cell Answer State : Type} [DecidableEq Cell]

def read (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (table : Cell → Answer) : List Node → State → State
  | [], state => state
  | node :: nodes, state => read input advance table nodes (advance node (table (input node state)) state)

def Separated (input : Node → State → Cell) : Prop :=
  ∀ left right, left ≠ right → ∀ before after, input left before ≠ input right after

omit [DecidableEq Cell] in
theorem read_congr (input : Node → State → Cell) (advance : Node → Answer → State → State)
    (left right : Cell → Answer) (hagrees : ∀ node state, left (input node state) = right (input node state))
    (nodes : List Node) (state : State) : read input advance left nodes state = read input advance right nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes ih =>
      simp only [read, hagrees]
      exact ih _

theorem read_update_of_not_mem (input : Node → State → Cell)
    (advance : Node → Answer → State → State) (hsep : Separated input)
    (table : Cell → Answer) (nodes : List Node) (node : Node) (hnode : node ∉ nodes)
    (before state : State) (answer : Answer) :
    read input advance (Function.update table (input node before) answer) nodes state =
      read input advance table nodes state := by
  induction nodes generalizing state with
  | nil => rfl
  | cons first rest ih =>
      have hne : first ≠ node := fun h => hnode (by simp [h])
      have hrest : node ∉ rest := fun h => hnode (List.mem_cons_of_mem _ h)
      simp only [read, Function.update_of_ne (hsep first node hne state before)]
      exact ih hrest _

variable [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer]
  [SampleableType Answer] [SampleableType (Cell → Answer)]

noncomputable def plant (input : Node → State → Cell)
    (advance : Node → Answer → State → State) : List Node → State → ProbComp (State × (Cell → Answer))
  | [], state => do
      let table ← $ᵗ (Cell → Answer)
      pure (state, table)
  | node :: nodes, state => do
      let answer ← $ᵗ Answer
      let result ← plant input advance nodes (advance node answer state)
      pure (result.1, Function.update result.2 (input node state) answer)

theorem evalDist_table_extract {Result : Type} (cell : Cell)
    (next : (Cell → Answer) → Answer → ProbComp Result) :
    𝒟[do let table ← ($ᵗ (Cell → Answer) : ProbComp _); next table (table cell)] =
      𝒟[do
        let answer ← ($ᵗ Answer : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        next (Function.update table cell answer) answer] := by
  have h := congrArg (fun distribution : SPMF (Cell → Answer) =>
    distribution >>= fun table => 𝒟[next table (table cell)])
    (evalDist_uniformSample_bind_update (R := Answer) cell)
  simpa only [evalDist_bind, bind_assoc, evalDist_pure, pure_bind, Function.update_self] using h.symm

theorem evalDist_read_eq_plant (input : Node → State → Cell)
    (advance : Node → Answer → State → State) (hsep : Separated input)
    (nodes : List Node) (hnodes : nodes.Nodup) (state : State) :
    𝒟[do
      let table ← ($ᵗ (Cell → Answer) : ProbComp _)
      pure (read input advance table nodes state, table)] =
      𝒟[plant input advance nodes state] := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node nodes ih =>
      obtain ⟨hnode, hnodes⟩ := List.nodup_cons.mp hnodes
      simp only [read]
      rw [evalDist_table_extract (input node state)
        (fun table answer => pure (read input advance table nodes (advance node answer state), table))]
      simp_rw [read_update_of_not_mem input advance hsep _ nodes node hnode]
      change 𝒟[do
        let answer ← ($ᵗ Answer : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        pure (read input advance table nodes (advance node answer state),
          Function.update table (input node state) answer)] = _
      simp only [plant]
      apply evalDist_bind_congr_left
      intro answer
      have h := congrArg (fun distribution : SPMF (State × (Cell → Answer)) =>
        distribution >>= fun result => pure (result.1, Function.update result.2 (input node state) answer))
        (ih hnodes (advance node answer state))
      simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h

theorem evalDist_read_bind_eq_plant {Result : Type} (input : Node → State → Cell)
    (advance : Node → Answer → State → State) (hsep : Separated input)
    (nodes : List Node) (hnodes : nodes.Nodup) (state : State)
    (next : State → (Cell → Answer) → ProbComp Result) :
    𝒟[do
      let table ← ($ᵗ (Cell → Answer) : ProbComp _)
      next (read input advance table nodes state) table] =
      𝒟[do let result ← plant input advance nodes state; next result.1 result.2] := by
  have h := congrArg (fun distribution : SPMF (State × (Cell → Answer)) =>
    distribution >>= fun result => 𝒟[next result.1 result.2])
    (evalDist_read_eq_plant input advance hsep nodes hnodes state)
  simpa only [evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h

noncomputable def draw (advance : Node → Answer → State → State) : List Node → State → ProbComp State
  | [], state => pure state
  | node :: nodes, state => do
      let answer ← $ᵗ Answer
      draw advance nodes (advance node answer state)

omit [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer] in
theorem evalDist_plant_fst (input : Node → State → Cell)
    (advance : Node → Answer → State → State) (nodes : List Node) (state : State) :
    𝒟[Prod.fst <$> plant input advance nodes state] = 𝒟[draw advance nodes state] := by
  induction nodes generalizing state with
  | nil =>
      simp only [plant, draw, map_bind, map_pure]
      exact evalDist_bind_const_neverFails _ (by simp) _
  | cons node nodes ih =>
      simp only [plant, draw, map_bind, map_pure]
      apply evalDist_bind_congr_left
      intro answer
      rw [bind_pure_comp]
      exact ih (advance node answer state)

omit [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer] in
theorem evalDist_plant_read {View Result : Type} (input : Node → State → Cell)
    (advance : Node → Answer → State → State) (nodes : List Node) (state : State)
    (view : State → (Cell → Answer) → View)
    (hview : ∀ node before after table answer,
      view after (Function.update table (input node before) answer) = view after table)
    (next : State → View → ProbComp Result) :
    𝒟[do let result ← plant input advance nodes state; next result.1 (view result.1 result.2)] =
      𝒟[do
        let result ← draw advance nodes state
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        next result (view result table)] := by
  induction nodes generalizing state with
  | nil => simp only [plant, draw, bind_assoc, pure_bind]
  | cons node nodes ih =>
      simp only [plant, draw, bind_assoc, pure_bind, hview]
      apply evalDist_bind_congr_left
      intro answer
      exact ih (advance node answer state)

omit [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer]
  [SampleableType Answer] [SampleableType (Cell → Answer)] in
theorem read_coordinate_table (table : Cell → Answer) (nodes : List Cell) (state : Cell → Answer) :
    read (fun node (_ : Cell → Answer) => node) (fun node output values => Function.update values node output)
      table nodes state = fun node => if node ∈ nodes then table node else state node := by
  induction nodes generalizing state with
  | nil => simp [read]
  | cons first rest ih =>
      rw [read, ih]
      funext node
      by_cases hrest : node ∈ rest <;> by_cases hfirst : node = first <;>
        simp [hrest, hfirst]

theorem evalDist_draw_coordinates (nodes : List Cell) (hnodup : nodes.Nodup)
    (hfull : ∀ node : Cell, node ∈ nodes) (state : Cell → Answer) :
    𝒟[draw (fun node output values => Function.update values node output) nodes state] =
      𝒟[($ᵗ (Cell → Answer) : ProbComp _)] := by
  let input := fun (node : Cell) (_ : Cell → Answer) => node
  let advance := fun (node : Cell) (output : Answer) (values : Cell → Answer) => Function.update values node output
  have h := congrArg (fun distribution : SPMF ((Cell → Answer) × (Cell → Answer)) =>
    Prod.fst <$> distribution)
    (evalDist_read_eq_plant input advance (fun _ _ h _ _ => h) nodes hnodup state)
  have hread : ∀ table : Cell → Answer, read input advance table nodes state = table := by
    intro table
    rw [read_coordinate_table]
    funext node
    rw [if_pos (hfull node)]
  have hmap :
      𝒟[Prod.fst <$> (do
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        pure (read input advance table nodes state, table))] =
        𝒟[Prod.fst <$> plant input advance nodes state] := by
    simpa only [evalDist_map] using h
  rw [evalDist_plant_fst] at hmap
  simpa only [map_bind, map_pure, hread, bind_pure] using hmap.symm

end SphincsSecurity.Concrete.FiniteGraphSampling
