import SphincsSecurity.Proof.OtsProbeNativeRootOuterCut

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runNativeOuterCut_query_is_unsafe
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (safe : (OracleWorld + SigningSpec).Domain → DeferredContext → Prop)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (OuterQueryCut α × SplitHashCache))
    (hresult : some result ∈ support (runNativeOuterCut impl safe computation context fuel table cache))
    (input : (OracleWorld + SigningSpec).Domain) (hinput : result.value.1.input? = some input) :
    ¬safe input result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value =>
      simp only [runNativeOuterCut, OracleComp.construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      contradiction
  | query_bind query next ih =>
      rw [runNativeOuterCut_query_bind] at hresult
      by_cases hsafe : safe query context
      · rw [if_pos hsafe, mem_support_bind_iff] at hresult
        obtain ⟨middle, hmiddle, htail⟩ := hresult
        cases middle with
        | none => simp at htail
        | some middle => exact ih middle.value.1 middle.context middle.remaining middle.table middle.value.2 htail
      · rw [if_neg hsafe] at hresult
        simp only [mem_support_pure_iff, Option.some.injEq] at hresult
        subst result
        have heq : query = input := Option.some.inj hinput
        subst input
        exact hsafe

theorem nativeRootOuterCut_query_is_unsafe_hash
    (parameter : PublicParameter) (root : Digest) (target : Position) (before after : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (OuterQueryCut α × SplitHashCache))
    (hresult : some result ∈ support
      (runNativeOuterCut (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (NativeRootOuterSafe parameter target before after) computation context fuel table cache))
    (input : (OracleWorld + SigningSpec).Domain) (hinput : result.value.1.input? = some input) :
    ∃ hashInput, input = .inl (.inr hashInput) ∧
      ¬NativeRootHashSafe parameter target before after hashInput result.context := by
  have hunsafe := runNativeOuterCut_query_is_unsafe _ _ computation context fuel table cache result hresult input hinput
  cases input with
  | inl query =>
      cases query with
      | inl n => exact False.elim (hunsafe trivial)
      | inr hashInput => exact ⟨hashInput, rfl, hunsafe⟩
  | inr message => exact False.elim (hunsafe trivial)

theorem nativeRootHashSafe_failure_classify
    (parameter : PublicParameter) (target : Position) (before after : HashOutput)
    (input : HashInput) (context : DeferredContext)
    (hunsafe : ¬NativeRootHashSafe parameter target before after input context) :
    ¬RootInputAvoids parameter target (truncateHash before) (truncateHash after) input ∨
      (∃ candidate, (purePlanProbingHashQuery parameter input (replaceNativePosition target before context).state).candidate? = some candidate ∧
        IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)) ∨
      ¬NativeRootActionSafe parameter target input (replaceNativePosition target before context)
        (replaceNativePosition target after context)
        (purePlanProbingHashQuery parameter input (replaceNativePosition target before context).state).action := by
  unfold NativeRootHashSafe at hunsafe
  by_cases hencoding : RootInputAvoids parameter target (truncateHash before) (truncateHash after) input
  · by_cases hprobe : ∀ candidate,
        (purePlanProbingHashQuery parameter input (replaceNativePosition target before context).state).candidate? = some candidate →
          ¬IsPrivateValueExposure target before after (.probe candidate.coordinate candidate.candidate)
    · exact Or.inr (Or.inr (fun haction => hunsafe ⟨hencoding, hprobe, haction⟩))
    · push Not at hprobe
      exact Or.inr (Or.inl hprobe)
  · exact Or.inl hencoding

end SphincsSecurity.Concrete.OtsProbeSimulation
