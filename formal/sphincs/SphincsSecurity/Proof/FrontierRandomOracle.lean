import SphincsSecurity.Proof.FrontierGameProjection
import SphincsSecurity.Proof.FiniteHashWorld

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] hashInputs boundaryEval fixedBoundaryRun

theorem evalDist_boundaryRun_eq_finiteHash {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (inputs : Finset HashInput)
    (hinputs : hashInputs (boundaryComputation parameter computation) ⊆ inputs) (cache : QueryCache HashSpec) :
    𝒟[Prod.fst <$> boundaryRun parameter computation cache] =
      𝒟[do
        let table ← sampleHashTable inputs
        fixedBoundaryRun parameter (finiteHashAnswer cache inputs table) computation] := by
  rw [boundaryRun_fst_eq_boundaryComputation, evalDist_romRun_eq_finiteHash _ inputs hinputs cache]
  apply evalDist_bind_congr_left
  intro table
  rw [fixedBoundaryRun_eq_boundaryComputation]

theorem evalDist_boundaryRun_signWithView_canonical (key : SecretKey) (message : Message)
    (inputs : Finset HashInput) (hinputs : hashInputs (boundaryComputation key.parameter (signWithView key message)) ⊆ inputs)
    (cache : QueryCache HashSpec) (dummy : OtsReferenceWords) :
    𝒟[Prod.fst <$> boundaryRun key.parameter (signWithView key message) cache] =
      𝒟[do
        let table ← sampleHashTable inputs
        let f := finiteHashAnswer cache inputs table
        let words := canonicalReferenceWords key f dummy
        frontierSigningRecord key.parameter key.root f key.ftsSecret words (canonicalFrontierValues key f words) message] := by
  rw [evalDist_boundaryRun_eq_finiteHash key.parameter _ inputs hinputs cache]
  apply evalDist_bind_congr_left
  intro table
  rw [fixedBoundaryRun_signWithView_canonical key _ dummy message]

theorem simulateQ_fixedHashWorld_lift_prob {α : Type} (f : QueryImpl HashSpec Id) (computation : ProbComp α) :
    simulateQ (fixedHashWorld f) (liftM computation) = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [liftM_bind, simulateQ_bind]
      have hquery : simulateQ (fixedHashWorld f)
          (liftM (liftM (unifSpec.query input) : ProbComp _)) = (liftM (unifSpec.query input) : ProbComp _) := by
        change simulateQ (fixedHashWorld f) (liftM (OracleWorld.query (.inl input))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [hquery]
      exact bind_congr ih

noncomputable def boundaryGameCore (adversary : Adversary) : OracleComp OracleWorld (Bool × SigningBoundaryTrace) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  boundaryComputation parameter (gameAfterSecrets adversary parameter otsSecret ftsSecret)

theorem boundaryComputation_fst {α : Type} (parameter : PublicParameter) (computation : OracleComp OracleWorld α) :
    Prod.fst <$> boundaryComputation parameter computation = computation := by
  rw [boundaryComputation, QueryImpl.fst_map_run_withTrace, simulateQ_id']

theorem boundaryGameCore_fst (adversary : Adversary) :
    Prod.fst <$> boundaryGameCore adversary = gameCore scheme adversary := by
  rw [gameCore_eq_secrets, boundaryGameCore]
  simp only [map_bind, boundaryComputation_fst]

noncomputable def fixedFrontierGame (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
  let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
  let words := canonicalReferenceWords key f dummy
  frontierGame parameter f ftsSecret words (canonicalFrontierValues key f words) adversary

theorem simulateQ_boundaryGameCore_frontier (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) :
    simulateQ (fixedHashWorld f) (boundaryGameCore adversary) = fixedFrontierGame f dummy adversary := by
  rw [boundaryGameCore, fixedFrontierGame]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro otsSecret
  apply bind_congr
  intro ftsSecret
  rw [← fixedBoundaryRun_eq_boundaryComputation, fixedBoundaryRun_gameAfterSecrets_canonical]

noncomputable def frontierOracleGame (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let table ← sampleHashTable inputs
  fixedFrontierGame (finiteHashAnswer ∅ inputs table) dummy adversary

theorem evalDist_boundaryGameCore_frontier (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒟[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      𝒟[frontierOracleGame inputs dummy adversary] := by
  rw [evalDist_romRun_eq_finiteHash _ inputs hinputs ∅, frontierOracleGame]
  apply evalDist_bind_congr_left
  intro table
  rw [simulateQ_boundaryGameCore_frontier _ dummy adversary]

theorem evalDist_gameCore_frontier (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒟[(simulateQ romImpl (gameCore scheme adversary)).run' ∅] =
      𝒟[Prod.fst <$> frontierOracleGame inputs dummy adversary] := by
  rw [← boundaryGameCore_fst, simulateQ_map, StateT.run'_eq, StateT.run_map]
  simp only [← LawfulFunctor.comp_map, Function.comp_def]
  rw [evalDist_map]
  have h := congrArg (fun distribution : SPMF (Bool × SigningBoundaryTrace) => Prod.fst <$> distribution)
    (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs)
  simpa only [StateT.run'_eq, evalDist_map, ← LawfulFunctor.comp_map, Function.comp_def] using h

theorem forgeAdvantage_eq_frontier (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.1 = true |
        frontierOracleGame (hashInputs (boundaryGameCore adversary)) dummy adversary] := by
  rw [forgeAdvantage]
  have h := evalDist_gameCore_frontier (hashInputs (boundaryGameCore adversary)) dummy adversary (Finset.Subset.refl _)
  rw [probOutput_congr rfl h, probOutput_map]

theorem boundaryRun_hashCalls_le {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (q : Nat) (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (cache : QueryCache HashSpec) (result : (α × SigningBoundaryTrace) × QueryCache HashSpec)
    (hresult : result ∈ support (boundaryRun parameter computation cache)) : result.1.2.hashCalls ≤ q := by
  have h := boundaryRun_bind_query_bound parameter computation (pure : α → OracleComp OracleWorld α) q
    (by rw [bind_pure]; exact hbound) cache result hresult
  exact h.1

theorem boundaryGameCore_hashCalls_le (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : Bool × SigningBoundaryTrace)
    (hresult : result ∈ support ((simulateQ romImpl (boundaryGameCore adversary)).run' ∅)) :
    result.2.hashCalls ≤ q := by
  rw [boundaryGameCore, simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨parameter, hparameter, hresult⟩ := hresult
  rw [simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨otsSecret, hots, hresult⟩ := hresult
  rw [simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨ftsSecret, hfts, hresult⟩ := hresult
  rw [← boundaryRun_fst_eq_boundaryComputation, support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact boundaryRun_hashCalls_le parameter _ q
    (isQueryBoundP_gameAfterSecrets adversary q hbound hparameter hots hfts) ∅ record hrecord

theorem frontierOracleGame_hashCalls_le_of_inputs (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : Bool × SigningBoundaryTrace)
    (hresult : result ∈ support (frontierOracleGame inputs dummy adversary)) :
    result.2.hashCalls ≤ q := by
  apply boundaryGameCore_hashCalls_le adversary q hbound result
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs)
    result).mpr hresult

theorem frontierOracleGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : Bool × SigningBoundaryTrace)
    (hresult : result ∈ support (frontierOracleGame (hashInputs (boundaryGameCore adversary)) dummy adversary)) :
    result.2.hashCalls ≤ q :=
  frontierOracleGame_hashCalls_le_of_inputs _ dummy adversary (Finset.Subset.refl _) q hbound result hresult

end SphincsSecurity.Concrete
