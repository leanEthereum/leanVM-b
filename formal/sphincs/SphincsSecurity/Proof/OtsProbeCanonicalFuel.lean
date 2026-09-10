import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeQueryCutPrehit
import SphincsSecurity.Proof.OtsProbeQueryTraceCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem fuel_bounds_of_mem_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table computation)) :
    result.remaining ≤ fuel ∧ fuel ≤ result.remaining + bound := by
  induction computation using OracleComp.inductionOn generalizing context fuel bound table with
  | pure value =>
      simp only [runResolvedFromTable, OracleComp.construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      exact ⟨le_rfl, Nat.le_add_right _ _⟩
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel bound table (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) htail
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel bound table (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) htail
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () _ fuel bound table (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hresult
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [runResolvedFromTable_probe_query_bind] at hresult
          | succ fuel =>
              have hpositive : 0 < bound := by simpa [LazyRevealProbe.IsProbe] using hbound.1
              rw [runResolvedFromTable_probe_query_bind] at hresult
              split_ifs at hresult
              · have htail := ih () context fuel (bound - 1) table
                  (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hresult
                omega
              · have htail := ih () _ fuel (bound - 1) table
                  (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hresult
                omega
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih _ context fuel bound table (by simpa [LazyRevealProbe.IsProbe] using hbound.2 _) hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () _ fuel bound table (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate <;> rw [mem_support_bind_iff] at hresult
          all_goals
            obtain ⟨resolvedOption, _hresolved, htail⟩ := hresult
            cases resolvedOption with
            | none => simp at htail
            | some resolved =>
                exact ih resolved.output _ fuel bound table (by simpa [LazyRevealProbe.IsProbe] using hbound.2 resolved.output) htail

def outerHashQueryCount : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inr _input) => 1
  | _ => 0

theorem maskedChronologicalExpandedAdversaryImpl_probeBound
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (cache : SplitHashCache) :
    ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache).IsQueryBoundP
      LazyRevealProbe.IsProbe (outerHashQueryCount input) := by
  cases input with
  | inl query =>
      cases query with
      | inl n => exact splitUniformImpl_probeFree n cache
      | inr input => exact probingHashQuery_run_isProbeBound parameter input cache
  | inr message => exact maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache

def canonicalTraceHashCount (history : List CanonicalQuerySelection) : Nat :=
  (history.map fun entry => outerHashQueryCount entry.input).sum

def prehitTraceHashCount (history : List PrehitQuerySnapshot) : Nat :=
  (history.map fun entry => outerHashQueryCount entry.input).sum

set_option maxRecDepth 100000 in
theorem prehitTraceHashCount_le_of_expanded
    (accountingKey secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl secretKey) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (state : ViewedFullTraceState × Bool)
    (result : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot)
    (hrun : result ∈ support (runPrehitQueryTrace accountingKey secretKey computation state)) :
    prehitTraceHashCount result.2 ≤ q := by
  induction computation using OracleComp.inductionOn generalizing q state result with
  | pure value =>
      simp only [runPrehitQueryTrace, OracleComp.construct_pure, mem_support_pure_iff] at hrun
      subst result
      simp [prehitTraceHashCount]
  | query_bind input next ih =>
      rw [runPrehitQueryTrace_query_bind, mem_support_bind_iff] at hrun
      obtain ⟨step, hstep, hrun⟩ := hrun
      rw [mem_support_bind_iff] at hrun
      obtain ⟨tail, htail, hpure⟩ := hrun
      simp only [mem_support_pure_iff] at hpure
      subst result
      have hactual : (step.1, step.2.1.cache) ∈ support
          ((unloggedMappedAdversaryImpl secretKey input).run state.1.cache) := by
        have hprojection := encodingPrehitViewedAdversaryImpl_cache_projection accountingKey secretKey
          ((OracleWorld + SigningSpec).query input) state
        simp only [simulateQ_spec_query] at hprojection
        rw [← hprojection, support_map]
        exact ⟨step, hstep, rfl⟩
      have houtput := unloggedMappedAdversaryImpl_output_mem_support_expanded secretKey input
        state.1.cache step.2.1.cache step.1 hactual
      cases input with
      | inl worldInput =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inl, OracleComp.isQueryBoundP_query_bind_iff] at hbound
          cases worldInput with
          | inl uniformInput =>
              have htailBound := ih step.1 q (hbound.2 step.1) step.2 tail htail
              simpa [prehitTraceHashCount, outerHashQueryCount] using htailBound
          | inr hashInput =>
              have hpositive : 0 < q := hbound.1.resolve_left (by simp)
              have htailBound := ih step.1 (q - 1) (hbound.2 step.1) step.2 tail htail
              change 1 + prehitTraceHashCount tail.2 ≤ q
              omega
      | inr request =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          have htailBound := ih step.1 q (isQueryBoundP_of_bind hbound step.1 houtput) step.2 tail htail
          simpa [prehitTraceHashCount, outerHashQueryCount] using htailBound

theorem CanonicalQueryTraceRel.hashCount_le
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection}
    {right : (α × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot}
    (hrelation : CanonicalQueryTraceRel parameter table left right) :
    canonicalTraceHashCount left.2 ≤ prehitTraceHashCount right.2 := by
  have hsum : ∀ (source : List CanonicalQuerySelection) (actual : List PrehitQuerySnapshot),
      List.Forall₂ (fun a b => CanonicalQuerySelectionRel parameter table (some a) (some b.actual)) source actual →
      canonicalTraceHashCount source = prehitTraceHashCount actual := by
    intro source actual hpaired
    induction hpaired with
    | nil => rfl
    | cons hhead _ ih =>
        simp only [canonicalTraceHashCount, prehitTraceHashCount, List.map_cons, List.sum_cons] at ih ⊢
        rw [hhead.1, ih]
        rfl
  have heq := hsum _ _ hrelation.2
  rw [heq]
  exact ((List.take_sublist _ _).map _).sum_le_sum (fun _ _ => Nat.zero_le _)

end SphincsSecurity.Concrete.OtsProbeSimulation
