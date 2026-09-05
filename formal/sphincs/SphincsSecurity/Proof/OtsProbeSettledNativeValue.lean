import SphincsSecurity.Proof.OtsProbeNativeRootQueryCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem IsOtsPosition.child {position child : Position}
    (hots : IsOtsPosition position) (hchild : child ∈ position.children) : IsOtsPosition child := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      simp only [Position.children] at hchild
      split_ifs at hchild <;> simp_all [IsOtsPosition]
  | leaf lay tree leafIdx =>
      simp only [Position.children, List.mem_ofFn] at hchild
      obtain ⟨chainIdx, rfl⟩ := hchild
      trivial
  | node lay tree level nodeIdx =>
      simp only [Position.children] at hchild
      split_ifs at hchild <;> simp_all [IsOtsPosition]
      all_goals rcases hchild with rfl | rfl <;> trivial
  | ftsLeaf | ftsNode | ftsRoots => contradiction

theorem ChronologicalCacheAgrees.computed_value_of_settled
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hcache : ChronologicalCacheAgrees parameter table context cache)
    (completion : Coordinate → HashOutput) (hcompletion : DeferredCompletion table context completion)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (position : Position) (hots : IsOtsPosition position)
    (hsettled : Settled parameter (tableOtsSecret completion) ftsSecret cache position) :
    DeferredPositionComputed context position ∧
      honestValue (fromCache cache) parameter (tableOtsSecret completion) ftsSecret position =
        tableValue completion position := by
  have hchildren : ∀ child ∈ position.children,
      DeferredPositionComputed context child ∧
        honestValue (fromCache cache) parameter (tableOtsSecret completion) ftsSecret child = tableValue completion child := by
    intro child hchild
    exact hcache.computed_value_of_settled completion hcompletion ftsSecret child (hots.child hchild)
      (hsettled.children child hchild)
  have hinput := honestInput_eq_tableInput_of_children (fromCache cache) parameter completion ftsSecret
    position hots hsettled.valid (fun child hchild => (hchildren child hchild).2)
  have hquery := hcache completion hcompletion position hots
  have hcached := hsettled.cached
  change cache (honestInput (fromCache cache) parameter (tableOtsSecret completion) ftsSecret position) ≠ none at hcached
  rw [hinput] at hcached
  cases hvalue : context.positionValue position with
  | none =>
      simp only [ResolveInputAgrees, hvalue] at hquery
      exact False.elim (hcached hquery)
  | some output =>
      simp only [ResolveInputAgrees, hvalue] at hquery
      refine ⟨.intro position hots hsettled.valid ⟨output, hvalue⟩ (fun child hchild => (hchildren child hchild).1), ?_⟩
      rw [honestValue, hinput, tableValue, hcompletion.eq_positionValue position output hvalue]
      simp [fromCache, hquery]
termination_by position.depth
decreasing_by exact Position.depth_lt_of_mem_children (by assumption)

theorem ResolvedContextInvariant.positionValue_of_settled
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache cache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context ordinaryCache cache)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    {position : Position} (hots : IsOtsPosition position)
    (hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position) :
    ∃ output, context.positionValue position = some output ∧
      honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret position = truncateHash output := by
  obtain ⟨completion, hcompletion⟩ := hinvariant.2.2.2.1
  have hkey : secretKey.otsSecret = tableOtsSecret completion := hsecrets.trans hcompletion.tableOtsSecret_eq.symm
  rw [hkey] at hsettled
  have hcomputed := hinvariant.1.computed_value_of_settled completion hcompletion secretKey.ftsSecret position hots hsettled
  cases hcomputed.1 with
  | intro _ _ _ hknown _ =>
      obtain ⟨output, houtput⟩ := hknown
      refine ⟨output, houtput, ?_⟩
      rw [hkey, hcomputed.2, tableValue, hcompletion.eq_positionValue position output houtput]

end SphincsSecurity.Concrete.OtsProbeSimulation
