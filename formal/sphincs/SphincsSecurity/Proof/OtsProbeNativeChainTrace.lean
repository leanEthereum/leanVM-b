import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeChainQuery
import SphincsSecurity.Proof.OtsProbeNativeQueryTrace

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

def NativeChainsPublished (trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection) : Prop :=
  (∀ result, trace.1 = some result → MaterializedChainsPublished result.context) ∧
    ∀ selection ∈ trace.2, MaterializedChainsPublished selection.context

def NativeChainTraceRel
    (left : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection)
    (right : α × QueryCache HashSpec) : Prop :=
  NativeChainsPublished left ∨ AnyEncodingInputsExhausted right.2

theorem relTriple_nativeChainTrace_of_public
    (left : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
    (right : ProbComp (α × QueryCache HashSpec))
    (hpublic : ∀ trace ∈ support left, NativeChainsPublished trace) :
    RelTriple left right NativeChainTraceRel := by
  apply relTriple_post_mono (FtsProbeSimulation.relTriple_and_left_support (relTriple_true left right) _ hpublic)
  intro trace result hrel
  exact Or.inl hrel.2

theorem relTriple_nativeChainTrace_of_exhausted
    (left : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection))
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (hexhausted : AnyEncodingInputsExhausted cache) :
    RelTriple left ((simulateQ (unloggedMappedAdversaryImpl secretKey) computation).run cache) NativeChainTraceRel := by
  apply relTriple_post_mono (FtsProbeSimulation.relTriple_and_right_support (relTriple_true left _))
  intro trace result hrel
  exact Or.inr (hexhausted.mono (FtsProbeSimulation.simulateQ_unloggedMappedAdversaryImpl_cache_le
    secretKey computation cache result.2 result.1 hrel.2))

theorem relTriple_nativeTrace_chainPublication
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) concreteCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) (hchain : MaterializedChainsPublished context) :
    RelTriple (runNativeQueryTrace parameter root ftsSecret computation context fuel table cache)
      ((simulateQ (unloggedMappedAdversaryImpl
        ⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩)
        computation).run concreteCache) NativeChainTraceRel := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache concreteCache with
  | pure value =>
      simp only [runNativeQueryTrace, OracleComp.construct_pure, if_pos hinvariant.2.2.2.1,
        simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      exact Or.inl ⟨by intro result heq; cases heq; exact hchain, by simp⟩
  | query_bind input next ih =>
      rw [runNativeQueryTrace_query_bind, if_pos hinvariant.2.2.2.1, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply relTriple_bind (relTriple_nativeQuery_chainFailure parameter root table ftsSecret input context fuel
        cache concreteCache hinvariant hvisible hpublished hchain)
      intro option right hrel
      by_cases hexhausted : AnyEncodingInputsExhausted right.2
      · exact relTriple_nativeChainTrace_of_exhausted _ _ (next right.1) right.2 hexhausted
      · cases option with
        | none =>
            apply relTriple_nativeChainTrace_of_public
            intro trace htrace
            simp only [pure_bind, mem_support_pure_iff] at htrace
            subst trace
            exact ⟨by simp, by simpa using hchain⟩
        | some result =>
            dsimp only
            rcases hrel.1 with hclean | hdoomed
            · rcases right with ⟨value, actualCache⟩
              have hvalue : result.value.1 = value := hclean.2.1
              subst value
              have hnextChain : MaterializedChainsPublished result.context := by
                rcases hrel.2 result rfl hclean.2.2.1.2.2.2.1 with hpublic | hfailure
                · exact hpublic
                · exact False.elim (hexhausted (anyEncodingInputsExhausted_of_cachedOtsEncodingFailure actualCache hfailure))
              have hnext := ih result.value.1 result.context result.remaining result.value.2 actualCache
                hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2 hnextChain
              let prepend := fun trace : Option (ResolvedRunResult (α × SplitHashCache)) × List CanonicalQuerySelection =>
                (trace.1, (⟨input, context, fuel, table, cache⟩ : CanonicalQuerySelection) :: trace.2)
              have hpost := relTriple_post_mono hnext (R' := fun trace final => NativeChainTraceRel (prepend trace) final) (by
                intro trace final htrace
                rcases htrace with htrace | hfailure
                · exact Or.inl ⟨htrace.1, by
                    intro selection hselection
                    rcases List.mem_cons.mp hselection with rfl | hmem
                    · exact hchain
                    · exact htrace.2 selection hmem⟩
                · exact Or.inr hfailure)
              have hmapped := relTriple_map (f := prepend) (g := id) hpost
              simpa only [hclean.1, prepend, map_eq_bind_pure_comp, Function.comp_def, id_eq, bind_pure] using hmapped
            · rw [runNativeQueryTrace_of_not_completable parameter root ftsSecret (next result.value.1)
                result.context result.remaining result.table result.value.2 (by rw [hdoomed.1]; exact hdoomed.2.2.2)]
              apply relTriple_nativeChainTrace_of_public
              intro trace htrace
              simp only [pure_bind, mem_support_pure_iff] at htrace
              subst trace
              exact ⟨by simp, by simpa using hchain⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
