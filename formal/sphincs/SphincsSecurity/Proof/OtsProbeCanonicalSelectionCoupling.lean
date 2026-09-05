import SphincsSecurity.Proof.OtsProbeCanonicalQuerySelection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

structure ActualQuerySelection where
  input : (OracleWorld + SigningSpec).Domain
  cache : QueryCache HashSpec

noncomputable def actualQuerySelection (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Nat → QueryCache HashSpec → ProbComp (Option ActualQuerySelection) :=
  OracleComp.construct (fun _ _ _ => pure none)
    (fun input _ next ordinal cache =>
      match ordinal with
      | 0 => pure (some ⟨input, cache⟩)
      | ordinal + 1 => do
          let result ← (unloggedMappedAdversaryImpl secretKey input).run cache
          next result.1 ordinal result.2) computation

def CanonicalQuerySelectionRel (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) :
    Option CanonicalQuerySelection → Option ActualQuerySelection → Prop
  | none, _ => True
  | some left, some right => left.input = right.input ∧ left.table = table ∧
      ResolvedContextInvariant parameter table left.context (ordinaryQueryCache left.cache) right.cache ∧
      VisibleResolvedComputationsCached parameter table left.context right.cache ∧
      PublishedValues left.context.state ∧ DeferredComputationsClosed left.context
  | some _, none => False

theorem canonicalQuerySelection_eq_none_of_not_completable
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnot : ¬DeferredCompletable table context) :
    canonicalQuerySelection parameter root ftsSecret computation ordinal context fuel table cache = pure none := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [canonicalQuerySelection_query_bind, if_neg hnot]

theorem relTriple_none_actualQuerySelection
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (right : ProbComp (Option ActualQuerySelection)) :
    RelTriple (pure none : ProbComp (Option CanonicalQuerySelection)) right
      (CanonicalQuerySelectionRel parameter table) := by
  have hbase := relTriple_true (pure none : ProbComp (Option CanonicalQuerySelection)) right
  have hsupported := FtsProbeSimulation.relTriple_and_left_support hbase
    (fun selection => selection = none) (by intro selection hselection; simpa using hselection)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  trivial

set_option maxRecDepth 100000 in
theorem relTriple_canonicalQuerySelection_actualQuerySelection
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    RelTriple (canonicalQuerySelection parameter root ftsSecret computation ordinal context fuel table cache)
      (actualQuerySelection
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey) computation ordinal actualCache)
      (CanonicalQuerySelectionRel parameter table) := by
  induction computation using OracleComp.inductionOn generalizing ordinal context fuel cache actualCache with
  | pure value => exact relTriple_pure_pure trivial
  | query_bind input next ih =>
      rw [canonicalQuerySelection_query_bind, if_pos hinvariant.2.2.2.1,
        actualQuerySelection, OracleComp.construct_query_bind]
      cases ordinal with
      | zero => exact relTriple_pure_pure ⟨rfl, rfl, hinvariant, hvisible, hpublished, hcomputed⟩
      | succ ordinal =>
          have hstep := canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl
            parameter root table ftsSecret input context fuel cache actualCache hinvariant hvisible hpublished
          have hsupported := FtsProbeSimulation.relTriple_and_left_support hstep
            (fun left => ∀ result, left = some result → DeferredComputationsClosed result.context) (by
              intro left hleft result heq
              subst left
              exact hcomputed.of_mem_canonicalChronologicalQuery parameter root table ftsSecret input context fuel cache
                result hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hleft)
          apply relTriple_bind hsupported
          intro left right hrelation
          cases left with
          | none => exact relTriple_none_actualQuerySelection parameter table _
          | some result =>
              dsimp only
              rcases hrelation.1 with hclean | hdoomed
              · rw [hclean.1, ← hclean.2.1]
                exact ih result.value.1 ordinal result.context result.remaining result.value.2 right.2
                  hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 (hrelation.2 result rfl)
              · rw [canonicalQuerySelection_eq_none_of_not_completable parameter root ftsSecret
                  (next result.value.1) ordinal result.context result.remaining result.table result.value.2 (by
                    rw [hdoomed.1]
                    exact hdoomed.2.2.2)]
                exact relTriple_none_actualQuerySelection parameter table _

end SphincsSecurity.Concrete.OtsProbeSimulation
