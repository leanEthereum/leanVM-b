import VCVio.ProgramLogic.Relational.FromUnary
import VCVio.ProgramLogic.Relational.SimulateQ

open OracleComp OracleSpec

namespace OracleComp.ProgramLogic.Relational

/-- Two stateful simulations stay synchronized while their states are related. A query may instead
move both sides into monotone bad states, after which their remaining executions may be coupled
arbitrarily. -/
theorem relTriple_simulateQ_run_until_bad
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {σ₁ σ₂ α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (hstep : ∀ (input : spec.Domain) (state₁ : σ₁) (state₂ : σ₂),
      related state₁ state₂ →
      RelTriple ((impl₁ input).run state₁) ((impl₂ input).run state₂)
        (fun result₁ result₂ =>
          (result₁.1 = result₂.1 ∧ related result₁.2 result₂.2) ∨
            (bad₁ result₁.2 ∧ bad₂ result₂.2)))
    (hmono₁ : ∀ (input : spec.Domain) (state : σ₁), bad₁ state →
      ∀ result ∈ support ((impl₁ input).run state), bad₁ result.2)
    (hmono₂ : ∀ (input : spec.Domain) (state : σ₂), bad₂ state →
      ∀ result ∈ support ((impl₂ input).run state), bad₂ result.2)
    (computation : OracleComp spec α) (state₁ : σ₁) (state₂ : σ₂)
    (hrelated : related state₁ state₂) :
    RelTriple
      ((simulateQ impl₁ computation).run state₁)
      ((simulateQ impl₂ computation).run state₂)
      (fun result₁ result₂ =>
        (result₁.1 = result₂.1 ∧ related result₁.2 result₂.2) ∨
          (bad₁ result₁.2 ∧ bad₂ result₂.2)) := by
  have hpreserve₁ : ∀ {β : Type} (continuation : OracleComp spec β)
      (state : σ₁), bad₁ state →
      ∀ result ∈ support ((simulateQ impl₁ continuation).run state),
        bad₁ result.2 := by
    intro β continuation
    induction continuation using OracleComp.inductionOn with
    | pure value =>
        intro state hbad result hresult
        simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        exact hbad
    | query_bind input next ih =>
        intro state hbad result hresult
        rw [simulateQ_query_bind, StateT.run_bind,
          mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        exact ih head.1 head.2
          (hmono₁ input state hbad head hhead) result htail
  have hpreserve₂ : ∀ {β : Type} (continuation : OracleComp spec β)
      (state : σ₂), bad₂ state →
      ∀ result ∈ support ((simulateQ impl₂ continuation).run state),
        bad₂ result.2 := by
    intro β continuation
    induction continuation using OracleComp.inductionOn with
    | pure value =>
        intro state hbad result hresult
        simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        exact hbad
    | query_bind input next ih =>
        intro state hbad result hresult
        rw [simulateQ_query_bind, StateT.run_bind,
          mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        exact ih head.1 head.2
          (hmono₂ input state hbad head hhead) result htail
  induction computation using OracleComp.inductionOn generalizing state₁ state₂ with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, hrelated⟩)
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind]
      apply relTriple_bind (hstep input state₁ state₂ hrelated)
      intro head₁ head₂ hhead
      rcases hhead with hgood | hbad
      · obtain ⟨hvalue, hstates⟩ := hgood
        rw [← hvalue]
        exact ih head₁.1 head₁.2 head₂.2 hstates
      · apply relTriple_post_mono
          (relTriple_prod
            (hpreserve₁ (next head₁.1) head₁.2 hbad.1)
            (hpreserve₂ (next head₂.1) head₂.2 hbad.2))
        intro result₁ result₂ hresults
        exact Or.inr hresults

/-- Two stateful simulations stay synchronized until the right state becomes bad. Once that
happens, only monotonicity of the right bad state is required. -/
theorem relTriple_simulateQ_run_until_bad_right
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {σ₁ σ₂ α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (related : σ₁ → σ₂ → Prop) (bad₂ : σ₂ → Prop)
    (hstep : ∀ (input : spec.Domain) (state₁ : σ₁) (state₂ : σ₂),
      related state₁ state₂ →
      RelTriple ((impl₁ input).run state₁) ((impl₂ input).run state₂)
        (fun result₁ result₂ =>
          (result₁.1 = result₂.1 ∧ related result₁.2 result₂.2) ∨
            bad₂ result₂.2))
    (hmono₂ : ∀ (input : spec.Domain) (state : σ₂), bad₂ state →
      ∀ result ∈ support ((impl₂ input).run state), bad₂ result.2)
    (computation : OracleComp spec α) (state₁ : σ₁) (state₂ : σ₂)
    (hrelated : related state₁ state₂) :
    RelTriple
      ((simulateQ impl₁ computation).run state₁)
      ((simulateQ impl₂ computation).run state₂)
      (fun result₁ result₂ =>
        (result₁.1 = result₂.1 ∧ related result₁.2 result₂.2) ∨
          bad₂ result₂.2) := by
  have hpreserve₂ : ∀ {β : Type} (continuation : OracleComp spec β)
      (state : σ₂), bad₂ state →
      ∀ result ∈ support ((simulateQ impl₂ continuation).run state),
        bad₂ result.2 := by
    intro β continuation
    induction continuation using OracleComp.inductionOn with
    | pure value =>
        intro state hbad result hresult
        simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        exact hbad
    | query_bind input next ih =>
        intro state hbad result hresult
        rw [simulateQ_query_bind, StateT.run_bind,
          mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        exact ih head.1 head.2
          (hmono₂ input state hbad head hhead) result htail
  induction computation using OracleComp.inductionOn generalizing state₁ state₂ with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, hrelated⟩)
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind]
      apply relTriple_bind (hstep input state₁ state₂ hrelated)
      intro head₁ head₂ hhead
      rcases hhead with hgood | hbad
      · obtain ⟨hvalue, hstates⟩ := hgood
        rw [← hvalue]
        exact ih head₁.1 head₁.2 head₂.2 hstates
      · apply relTriple_post_mono
          (relTriple_prod
            (fun _result _hresult => True.intro)
            (hpreserve₂ (next head₂.1) head₂.2 hbad))
        intro _result₁ _result₂ hresults
        exact Or.inr hresults.2

end OracleComp.ProgramLogic.Relational
