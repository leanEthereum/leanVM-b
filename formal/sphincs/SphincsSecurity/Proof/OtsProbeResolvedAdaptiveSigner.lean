import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedSchedule

/-!
# Canonical adaptive signer boundaries

A signer may materialize structural answers that it does not publish. At the return boundary these
answers move back into the deferred representation, so later adversarial guesses remain probeable.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def publicMaterializedValues (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (coordinate : Coordinate) : Option HashOutput :=
  if coordinate ∈ context.state.revealed then
    resolvedCompletionValue table context coordinate
  else none

def canonicalizeMaterializedValues (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : DeferredContext :=
  { context with
    state := { context.state with values := publicMaterializedValues table context } }

theorem canonicalizeMaterializedValues_positionValue
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) (position : Position) :
    (canonicalizeMaterializedValues table context).positionValue position =
      context.positionValue position := by
  unfold canonicalizeMaterializedValues DeferredContext.positionValue
    publicMaterializedValues
  by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
  · simp only [hrevealed, ↓reduceIte, resolvedCompletionValue]
    cases hstate : context.state.values (.position position) with
    | none =>
        cases hdeferred : context.values position <;>
          simp [DeferredContext.positionValue, hstate, hdeferred]
    | some output => simp [DeferredContext.positionValue, hstate]
  · simp only [hrevealed, ↓reduceIte]
    cases hvalue : context.state.values (.position position) with
    | none => simp
    | some output =>
        have hdeferred := hconsistent position output hvalue
        simp [hdeferred]

theorem canonicalizeMaterializedValues_resolvedCompletionValue
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) :
    resolvedCompletionValue table (canonicalizeMaterializedValues table context) =
      resolvedCompletionValue table context := by
  funext coordinate
  cases coordinate with
  | chainStart => rfl
  | position position =>
      exact canonicalizeMaterializedValues_positionValue table context hconsistent position

theorem canonicalizeMaterializedValues_valuesConsistent
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) :
    (canonicalizeMaterializedValues table context).ValuesConsistent := by
  intro position output hvalue
  unfold canonicalizeMaterializedValues publicMaterializedValues at hvalue
  by_cases hrevealed : Coordinate.position position ∈ context.state.revealed
  · simp only [hrevealed, ↓reduceIte] at hvalue
    have hresolved : context.positionValue position = some output := by
      simpa [resolvedCompletionValue] using hvalue
    change context.values position = some output
    unfold DeferredContext.positionValue at hresolved
    cases hstate : context.state.values (.position position) with
    | none => simpa [hstate] using hresolved
    | some cached =>
        have hcached : cached = output := by simpa [hstate] using hresolved
        subst cached
        exact hconsistent position output hstate
  · simp [hrevealed] at hvalue

theorem canonicalizeMaterializedValues_startTableAgrees
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    StartTableAgrees (canonicalizeMaterializedValues table context).state table := by
  intro index output hvalue
  unfold canonicalizeMaterializedValues publicMaterializedValues at hvalue
  by_cases hrevealed : index.coordinate ∈ context.state.revealed
  · simp only [hrevealed, ↓reduceIte] at hvalue
    have htable : table index = output := by
      simpa [resolvedCompletionValue, OtsSecretIndex.coordinate] using hvalue
    exact htable.symm
  · simp [hrevealed] at hvalue

theorem finalizationViewEq_canonicalize_left
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table)
    (hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output) :
    FinalizationViewEq table (canonicalizeMaterializedValues table context) context := by
  have hconsistent := hvalid.valuesConsistent
  have hvalueEq := canonicalizeMaterializedValues_resolvedCompletionValue table context hconsistent
  refine ⟨canonicalizeMaterializedValues_valuesConsistent table context hconsistent,
    hconsistent, canonicalizeMaterializedValues_startTableAgrees table context,
    hstarts, hvalueEq, ?_, hclean, ?_⟩
  · intro coordinate output hvalue
    have horiginal : resolvedCompletionValue table context coordinate = some output := by
      rw [← hvalueEq]
      exact hvalue
    change ¬context.state.hitAt coordinate output
    exact hclean coordinate output horiginal
  · intro coordinate hvalue
    rfl

theorem canonicalizeMaterializedValues_valid
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid)
    (hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output) :
    (canonicalizeMaterializedValues table context).Valid := by
  refine ⟨canonicalizeMaterializedValues_valuesConsistent table context
    hvalid.valuesConsistent, ?_⟩
  intro coordinate output hvalue
  unfold canonicalizeMaterializedValues publicMaterializedValues at hvalue
  by_cases hrevealed : coordinate ∈ context.state.revealed
  · simp only [hrevealed, ↓reduceIte] at hvalue
    change ¬context.state.hitAt coordinate output
    exact hclean coordinate output hvalue
  · simp [hrevealed] at hvalue

theorem DeferredCompletion.of_canonicalizeMaterializedValues
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hcompletion : DeferredCompletion table
      (canonicalizeMaterializedValues table context) completion) :
    DeferredCompletion table context completion := by
  refine ⟨?_, hcompletion.2.1, hcompletion.2.2.1, hcompletion.2.2.2⟩
  intro coordinate output hvalue
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
      have houtput : output = table index := hstarts index output hvalue
      rw [houtput]
      exact hcompletion.2.2.2 index
  | position position =>
      have hprivate := hconsistent position output hvalue
      exact hcompletion.2.1 position output hprivate

theorem DeferredCompletion.to_canonicalizedMaterializedValues
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion) :
    DeferredCompletion table (canonicalizeMaterializedValues table context) completion := by
  refine ⟨?_, hcompletion.2.1, hcompletion.2.2.1, hcompletion.2.2.2⟩
  intro coordinate output hvalue
  unfold canonicalizeMaterializedValues publicMaterializedValues at hvalue
  by_cases hrevealed : coordinate ∈ context.state.revealed
  · simp only [hrevealed, ↓reduceIte] at hvalue
    exact hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  · simp [hrevealed] at hvalue

theorem doomedResolvedContext_canonicalizeMaterializedValues
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hdoomed : DoomedResolvedContext table context) :
    DoomedResolvedContext table (canonicalizeMaterializedValues table context) := by
  refine ⟨canonicalizeMaterializedValues_valuesConsistent table context hdoomed.1,
    canonicalizeMaterializedValues_startTableAgrees table context, ?_⟩
  intro hcompletable
  rcases hcompletable with ⟨completion, hcompletion⟩
  exact hdoomed.2.2 ⟨completion,
    hcompletion.of_canonicalizeMaterializedValues hdoomed.1 hdoomed.2.1⟩

def canonicalizeResolvedRun (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult α) → Option (ResolvedRunResult α)
  | none => none
  | some result => some
      { result with context := canonicalizeMaterializedValues table result.context }

def ResolvedQueryImpl (spec : OracleSpec ι) :=
  (query : spec.Domain) → DeferredContext → Nat →
    (OtsSecretIndex → HashOutput) → SplitHashCache →
      ProbComp (Option (ResolvedRunResult (spec.Range query × SplitHashCache)))

noncomputable def canonicalChronologicalAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ResolvedQueryImpl (OracleWorld + SigningSpec) :=
  fun query context fuel _table cache =>
    match query with
    | .inl oracleQuery =>
        runResolvedFromTable context fuel table
            ((probingRomImpl parameter oracleQuery).run cache) >>=
          fun result => pure (canonicalizeResolvedRun table result)
    | .inr message =>
        runResolvedFromTable context fuel table
            ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache) >>=
          fun result => pure (canonicalizeResolvedRun table result)

theorem canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    canonicalChronologicalAdversaryImpl parameter root table ftsSecret
        input context fuel table cache =
      (runResolvedFromTable context fuel table
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache) >>=
          fun result => pure (canonicalizeResolvedRun table result)) := by
  cases input <;> rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
