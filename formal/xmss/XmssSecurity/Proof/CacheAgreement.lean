import XmssSecurity.Proof.CausalPairedKeygen

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def HashCachesAgreeOn (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec) : Prop :=
  ∀ input, inputs input → left input = right input

theorem HashCachesAgreeOn.cacheQuery
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn inputs left right)
    (input : HashInput) (output : HashOutput) :
    HashCachesAgreeOn inputs
      (left.cacheQuery input output) (right.cacheQuery input output) := by
  intro candidate hcandidate
  by_cases heq : candidate = input
  · subst candidate
    simp
  · rw [QueryCache.cacheQuery_of_ne left output heq,
      QueryCache.cacheQuery_of_ne right output heq]
    exact hagrees candidate hcandidate

theorem HashCachesAgreeOn.cacheQuery_distinct
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn inputs left right)
    (leftInput rightInput : HashInput) (output : HashOutput)
    (hleft : ∀ candidate, inputs candidate → candidate ≠ leftInput)
    (hright : ∀ candidate, inputs candidate → candidate ≠ rightInput) :
    HashCachesAgreeOn inputs
      (left.cacheQuery leftInput output)
      (right.cacheQuery rightInput output) := by
  intro candidate hcandidate
  rw [QueryCache.cacheQuery_of_ne left output (hleft candidate hcandidate),
    QueryCache.cacheQuery_of_ne right output (hright candidate hcandidate)]
  exact hagrees candidate hcandidate

theorem relTriple_randomOracle_run_of_cachesAgreeOn
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (input : HashInput) (hinput : inputs input)
    (hagrees : HashCachesAgreeOn inputs left right) :
    RelTriple
      ((randomOracle input).run left)
      ((randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        HashCachesAgreeOn.cacheQuery inputs left right hagrees
          input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl⟩

theorem relTriple_randomOracle_run_of_both_none
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (leftInput rightInput : HashInput)
    (hleftNone : left leftInput = none)
    (hrightNone : right rightInput = none)
    (hagrees : HashCachesAgreeOn inputs left right)
    (hleft : ∀ candidate, inputs candidate → candidate ≠ leftInput)
    (hright : ∀ candidate, inputs candidate → candidate ≠ rightInput) :
    RelTriple
      ((randomOracle leftInput).run left)
      ((randomOracle rightInput).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2) := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hleftNone,
    QueryImpl.withCaching_run_none _ hrightNone,
    map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
  intro leftOutput rightOutput houtput
  subst rightOutput
  exact relTriple_pure_pure ⟨rfl,
    HashCachesAgreeOn.cacheQuery_distinct inputs left right hagrees
      leftInput rightInput leftOutput hleft hright,
    QueryCache.le_cacheQuery left hleftNone,
    QueryCache.le_cacheQuery right hrightNone⟩

theorem relTriple_strengthen_support
    {alpha beta : Type}
    {left : ProbComp alpha} {right : ProbComp beta}
    {relation : alpha → beta → Prop}
    {leftProperty : alpha → Prop} {rightProperty : beta → Prop}
    (hrel : RelTriple left right relation)
    (hleft : ∀ result ∈ support left, leftProperty result)
    (hright : ∀ result ∈ support right, rightProperty result) :
    RelTriple left right (fun leftResult rightResult =>
      relation leftResult rightResult ∧
        leftProperty leftResult ∧ rightProperty rightResult) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel ⊢
  obtain ⟨coupling, hcoupling⟩ := hrel
  refine ⟨coupling, ?_⟩
  intro pair hpair
  have hleftSupportDist : pair.1 ∈ support 𝒟[left] := by
    rw [← coupling.2.map_fst, support_map]
    exact ⟨pair, hpair, rfl⟩
  have hrightSupportDist : pair.2 ∈ support 𝒟[right] := by
    rw [← coupling.2.map_snd, support_map]
    exact ⟨pair, hpair, rfl⟩
  have hleftSupport : pair.1 ∈ support left := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hleftSupportDist ⊢
    simpa using hleftSupportDist
  have hrightSupport : pair.2 ∈ support right := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hrightSupportDist ⊢
    simpa using hrightSupportDist
  exact ⟨hcoupling pair hpair,
    hleft pair.1 hleftSupport, hright pair.2 hrightSupport⟩

theorem relTriple_with_support
    {alpha beta : Type}
    {left : ProbComp alpha} {right : ProbComp beta}
    {relation : alpha → beta → Prop}
    (hrel : RelTriple left right relation) :
    RelTriple left right (fun leftResult rightResult =>
      relation leftResult rightResult ∧
        leftResult ∈ support left ∧ rightResult ∈ support right) :=
  relTriple_strengthen_support hrel
    (fun _ hresult => hresult) (fun _ hresult => hresult)


end XmssSecurity
