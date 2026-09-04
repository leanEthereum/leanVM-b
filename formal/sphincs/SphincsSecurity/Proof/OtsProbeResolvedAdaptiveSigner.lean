import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveFinalization

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

def CanonicalMaterializedValues (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : Prop :=
  context.state.values = publicMaterializedValues table context

theorem canonicalizeMaterializedValues_revealed
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    (canonicalizeMaterializedValues table context).state.revealed =
      context.state.revealed := rfl

theorem canonicalizeMaterializedValues_pending
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    (canonicalizeMaterializedValues table context).state.pending =
      context.state.pending := rfl

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

theorem canonicalizeMaterializedValues_canonical
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) :
    CanonicalMaterializedValues table
      (canonicalizeMaterializedValues table context) := by
  change publicMaterializedValues table context =
    publicMaterializedValues table (canonicalizeMaterializedValues table context)
  funext coordinate
  unfold publicMaterializedValues
  by_cases hrevealed : coordinate ∈ context.state.revealed
  · have hcanonicalRevealed : coordinate ∈
        (canonicalizeMaterializedValues table context).state.revealed := hrevealed
    simp only [hrevealed, hcanonicalRevealed, ↓reduceIte]
    rw [canonicalizeMaterializedValues_resolvedCompletionValue table context hconsistent]
  · have hcanonicalNotRevealed : coordinate ∉
        (canonicalizeMaterializedValues table context).state.revealed := hrevealed
    simp [hrevealed, hcanonicalNotRevealed]

theorem canonicalizeMaterializedValues_idempotent
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent) :
    canonicalizeMaterializedValues table
        (canonicalizeMaterializedValues table context) =
      canonicalizeMaterializedValues table context := by
  have hcanonical := canonicalizeMaterializedValues_canonical table context hconsistent
  unfold CanonicalMaterializedValues at hcanonical
  cases context with
  | mk state values =>
      cases state with
      | mk pending stateValues revealed ensured =>
          simp only [canonicalizeMaterializedValues] at hcanonical ⊢
          rw [← hcanonical]

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

theorem publicMaterializedValues_eq_of_finalizationViewEq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hview : FinalizationViewEq table left right)
    (hrevealed : left.state.revealed = right.state.revealed) :
    publicMaterializedValues table left = publicMaterializedValues table right := by
  funext coordinate
  by_cases hleftRevealed : coordinate ∈ left.state.revealed
  · have hrightRevealed : coordinate ∈ right.state.revealed := by
      rwa [← hrevealed]
    simp [publicMaterializedValues, hleftRevealed, hrightRevealed, hview.valueEq]
  · have hrightRevealed : coordinate ∉ right.state.revealed := by
      rwa [← hrevealed]
    simp [publicMaterializedValues, hleftRevealed, hrightRevealed]

theorem canonicalizedFinalizationContextEq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hrevealed : left.state.revealed = right.state.revealed) :
    FinalizationContextEq table
        (some (canonicalizeMaterializedValues table left))
        (some (canonicalizeMaterializedValues table right)) ∧
      (canonicalizeMaterializedValues table left).state.values =
        (canonicalizeMaterializedValues table right).state.values := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hleftCanonicalView := finalizationViewEq_canonicalize_left table left hleftValid
    hview.leftStarts hview.leftClean
  have hrightCanonicalView := finalizationViewEq_canonicalize_left table right hrightValid
    hview.rightStarts hview.rightClean
  have hleftCanonicalValid := canonicalizeMaterializedValues_valid table left hleftValid
    hview.leftClean
  have hrightCanonicalValid := canonicalizeMaterializedValues_valid table right hrightValid
    hview.rightClean
  have hleftCanonicalCompletable : DeferredCompletable table
      (canonicalizeMaterializedValues table left) := by
    rcases hleftCompletable with ⟨completion, hcompletion⟩
    exact ⟨completion,
      (hleftCanonicalView.deferredCompletion_iff completion).mpr hcompletion⟩
  constructor
  · exact ⟨hleftCanonicalView.trans (hview.trans hrightCanonicalView.symm),
      hleftCanonicalValid, hrightCanonicalValid, hleftCanonicalCompletable⟩
  · exact publicMaterializedValues_eq_of_finalizationViewEq hview hrevealed

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

theorem ChronologicalCacheAgrees.to_canonicalizedMaterializedValues
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hagrees : ChronologicalCacheAgrees parameter table context cache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    ChronologicalCacheAgrees parameter table
      (canonicalizeMaterializedValues table context) cache := by
  intro completion hcompletion position hots
  have horiginal := hcompletion.of_canonicalizeMaterializedValues hconsistent hstarts
  have hknown := hagrees completion horiginal position hots
  unfold ResolveInputAgrees at hknown ⊢
  rw [canonicalizeMaterializedValues_positionValue table context hconsistent]
  exact hknown

theorem ResolvedCachePartition.to_canonicalizedMaterializedValues
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table context ordinaryCache concreteCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    ResolvedCachePartition parameter table
      (canonicalizeMaterializedValues table context) ordinaryCache concreteCache := by
  refine ⟨hpartition.1, ?_⟩
  intro input output hcached
  rcases hpartition.2 input output hcached with hordinary | hfixed
  · exact Or.inl hordinary
  · rcases hfixed with ⟨position, hots, hvalue, hinput⟩
    right
    refine ⟨position, hots, ?_, ?_⟩
    · rw [canonicalizeMaterializedValues_positionValue table context hconsistent]
      exact hvalue
    · intro completion hcompletion
      exact hinput completion
        (hcompletion.of_canonicalizeMaterializedValues hconsistent hstarts)

theorem VisibleResolvedComputationsCached.to_canonicalizedMaterializedValues
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : VisibleResolvedComputationsCached parameter table context cache)
    (hpublished : PublishedValues context.state) :
    VisibleResolvedComputationsCached parameter table
      (canonicalizeMaterializedValues table context) cache := by
  intro position output hresolvable hvalue
  have hrevealed : Coordinate.position position ∈ context.state.revealed := by
    unfold canonicalizeMaterializedValues publicMaterializedValues at hvalue
    by_contra hnotRevealed
    simp [hnotRevealed] at hvalue
  have horiginalNonempty := hpublished (.position position) hrevealed
  cases horiginal : context.state.values (.position position) with
  | none => exact False.elim (horiginalNonempty horiginal)
  | some originalOutput =>
      have hresolved : resolvedCompletionValue table context (.position position) =
          some originalOutput := by
        simp [resolvedCompletionValue, DeferredContext.positionValue, horiginal]
      have houtput : originalOutput = output := by
        unfold canonicalizeMaterializedValues publicMaterializedValues at hvalue
        simp only [hrevealed, ↓reduceIte] at hvalue
        exact Option.some.inj (hresolved.symm.trans hvalue)
      subst originalOutput
      exact hclosed position output hresolvable horiginal

theorem PublishedValues.to_canonicalizedMaterializedValues
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hpublished : PublishedValues context.state) :
    PublishedValues (canonicalizeMaterializedValues table context).state := by
  intro coordinate hrevealed
  have hrevealedOriginal : coordinate ∈ context.state.revealed := by
    simpa [canonicalizeMaterializedValues] using hrevealed
  unfold canonicalizeMaterializedValues publicMaterializedValues
  simp only [hrevealedOriginal, ↓reduceIte]
  have horiginalNonempty := hpublished coordinate hrevealedOriginal
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [resolvedCompletionValue]
  | position position =>
      cases horiginal : context.state.values (.position position) with
      | none => exact False.elim (horiginalNonempty horiginal)
      | some output =>
          simp [resolvedCompletionValue, DeferredContext.positionValue, horiginal]

theorem ResolvedContextInvariant.to_canonicalizedMaterializedValues
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache) :
    ResolvedContextInvariant parameter table
      (canonicalizeMaterializedValues table context) ordinaryCache concreteCache := by
  rcases hinvariant with ⟨hagrees, hvalid, hstarts, hcompletable, hpartition⟩
  refine ⟨hagrees.to_canonicalizedMaterializedValues hvalid.valuesConsistent hstarts,
    ?_, canonicalizeMaterializedValues_startTableAgrees table context, ?_,
    hpartition.to_canonicalizedMaterializedValues hvalid.valuesConsistent hstarts⟩
  · rcases hcompletable with ⟨completion, hcompletion⟩
    have hclean : ∀ coordinate output,
        resolvedCompletionValue table context coordinate = some output →
          ¬context.state.hitAt coordinate output := by
      intro coordinate output hvalue hhit
      have houtput := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
      unfold LazyRevealProbe.State.hitAt at hhit
      rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
      exact hcompletion.2.2.1 coordinate (truncateHash output) hhit (by rw [houtput])
    exact canonicalizeMaterializedValues_valid table context hvalid hclean
  · rcases hcompletable with ⟨completion, hcompletion⟩
    exact ⟨completion, hcompletion.to_canonicalizedMaterializedValues⟩

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

def CanonicalResolvedRun (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult α) → Prop
  | none => True
  | some result => CanonicalMaterializedValues table result.context

theorem canonicalResolvedRun_canonicalize
    (table : OtsSecretIndex → HashOutput)
    (result : Option (ResolvedRunResult α))
    (hconsistent : ∀ resolved, result = some resolved →
      resolved.context.ValuesConsistent) :
    CanonicalResolvedRun table (canonicalizeResolvedRun table result) := by
  cases result with
  | none => trivial
  | some result =>
      exact canonicalizeMaterializedValues_canonical table result.context
        (hconsistent result rfl)

theorem canonicalizeResolvedRun_idempotent
    (table : OtsSecretIndex → HashOutput)
    (result : Option (ResolvedRunResult α))
    (hconsistent : ∀ resolved, result = some resolved →
      resolved.context.ValuesConsistent) :
    canonicalizeResolvedRun table (canonicalizeResolvedRun table result) =
      canonicalizeResolvedRun table result := by
  cases result with
  | none => rfl
  | some result =>
      simp only [canonicalizeResolvedRun]
      rw [canonicalizeMaterializedValues_idempotent table result.context
        (hconsistent result rfl)]

theorem ReachableResolvedRunRel.canonicalizeResolvedRun
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (α × SplitHashCache))}
    {right : α × QueryCache HashSpec}
    (hrelation : ReachableResolvedRunRel parameter table left right) :
    ReachableResolvedRunRel parameter table (canonicalizeResolvedRun table left) right := by
  cases left with
  | none => trivial
  | some result =>
      rcases hrelation with hclean | hdoomed
      · left
        exact ⟨hclean.1, hclean.2.1,
          hclean.2.2.1.to_canonicalizedMaterializedValues,
          hclean.2.2.2.1.to_canonicalizedMaterializedValues hclean.2.2.2.2,
          hclean.2.2.2.2.to_canonicalizedMaterializedValues⟩
      · right
        exact ⟨hdoomed.1,
          doomedResolvedContext_canonicalizeMaterializedValues hdoomed.2⟩

theorem relTriple_canonicalizeResolvedRun_of_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (Option (ResolvedRunResult (α × SplitHashCache))))
    (rightRun : ProbComp (α × QueryCache HashSpec))
    (hrelation : RelTriple leftRun rightRun
      (ReachableResolvedRunRel parameter table)) :
    RelTriple
      (leftRun >>= fun result => pure (canonicalizeResolvedRun table result))
      rightRun (ReachableResolvedRunRel parameter table) := by
  rw [show rightRun = rightRun >>= pure by simp]
  apply relTriple_bind hrelation
  intro left right hresult
  exact relTriple_pure_pure hresult.canonicalizeResolvedRun

theorem finalizationSynchronizedRunEq_canonicalize
    (table : OtsSecretIndex → HashOutput)
    (left right : Option (ResolvedRunResult (α × SplitHashCache)))
    (hrelation : FinalizationAdaptiveRunEq table left right) :
    FinalizationSynchronizedRunEq table
      (canonicalizeResolvedRun table left) (canonicalizeResolvedRun table right) := by
  rcases hrelation with hclean | hdoomed
  · cases left with
    | none =>
        cases right with
        | none => exact Or.inl ⟨trivial, trivial⟩
        | some right => simp [FinalizationMaterializedRunEq] at hclean
    | some left =>
        cases right with
        | none => simp [FinalizationMaterializedRunEq] at hclean
        | some right =>
            rcases hclean with
              ⟨hvalue, hcontext, hremaining, hleftTable, hrightTable, hcache, hrevealed⟩
            obtain ⟨hcanonicalContext, hcanonicalValues⟩ :=
              canonicalizedFinalizationContextEq hcontext hrevealed
            left
            exact ⟨⟨hvalue, hcanonicalContext, hremaining, hleftTable, hrightTable,
              hcache, hrevealed⟩, hcanonicalValues⟩
  · right
    constructor
    · cases left with
      | none => trivial
      | some left =>
          exact ⟨hdoomed.1.1,
            doomedResolvedContext_canonicalizeMaterializedValues hdoomed.1.2⟩
    · cases right with
      | none => trivial
      | some right =>
          exact ⟨hdoomed.2.1,
            doomedResolvedContext_canonicalizeMaterializedValues hdoomed.2.2⟩

set_option maxRecDepth 100000 in
theorem relTriple_canonicalized_maskedPublishedChronologicalSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (left right : DeferredContext) (fuel : Nat) (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runResolvedFromTable left fuel table
          ((maskedPublishedChronologicalSign parameter root ftsSecret message).run leftCache) >>=
        fun result => pure (canonicalizeResolvedRun table result))
      (runDeferredChronologicalSign parameter root table ftsSecret message right fuel rightCache >>=
        fun result => pure (canonicalizeResolvedRun table result))
      (FinalizationSynchronizedRunEq table) := by
  apply relTriple_bind
    (relTriple_runResolvedFromTable_maskedPublishedChronologicalSign_finalization parameter root
      table ftsSecret message left right fuel leftCache rightCache hcontext hcache hrevealed)
  intro leftResult rightResult hrelation
  apply relTriple_pure_pure
  exact finalizationSynchronizedRunEq_canonicalize table leftResult rightResult
    (Or.inl hrelation)

def ResolvedQueryImpl (spec : OracleSpec ι) :=
  (query : spec.Domain) → DeferredContext → Nat →
    (OtsSecretIndex → HashOutput) → SplitHashCache →
      ProbComp (Option (ResolvedRunResult (spec.Range query × SplitHashCache)))

noncomputable def runSynchronizedResolved
    (impl : ResolvedQueryImpl spec) (computation : OracleComp spec α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (α × SplitHashCache))) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp spec α => DeferredContext → Nat →
      (OtsSecretIndex → HashOutput) → SplitHashCache →
        ProbComp (Option (ResolvedRunResult (α × SplitHashCache))))
    (fun value context remaining table cache =>
      if _hcompletable : DeferredCompletable table context then
        pure (some ⟨context, remaining, (value, cache), table⟩)
      else pure none)
    (fun query _next recursivelyRun context fuel table cache =>
      if _hcompletable : DeferredCompletable table context then do
        let stepOption : Option (ResolvedRunResult (spec.Range query × SplitHashCache)) ←
          impl query context fuel table cache
        match stepOption with
        | none => pure (none : Option (ResolvedRunResult (α × SplitHashCache)))
        | some result =>
            recursivelyRun result.value.1 result.context result.remaining result.table
              result.value.2
      else pure none)
    computation context fuel table cache

theorem runSynchronizedResolved_pure
    (impl : ResolvedQueryImpl spec) (value : α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcompletable : DeferredCompletable table context) :
    runSynchronizedResolved impl (pure value) context fuel table cache =
      pure (some ⟨context, fuel, (value, cache), table⟩) := by
  rw [runSynchronizedResolved, OracleComp.construct_pure]
  simp [hcompletable]

theorem runSynchronizedResolved_pure_of_not_completable
    (impl : ResolvedQueryImpl spec) (value : α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnotCompletable : ¬DeferredCompletable table context) :
    runSynchronizedResolved impl (pure value) context fuel table cache = pure none := by
  rw [runSynchronizedResolved, OracleComp.construct_pure]
  simp [hnotCompletable]

theorem runSynchronizedResolved_query_bind_of_not_completable
    (impl : ResolvedQueryImpl spec) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnotCompletable : ¬DeferredCompletable table context) :
    runSynchronizedResolved impl (liftM (spec.query query) >>= next)
        context fuel table cache = pure none := by
  rw [runSynchronizedResolved, OracleComp.construct_query_bind]
  simp [hnotCompletable]

theorem runSynchronizedResolved_of_not_completable
    (impl : ResolvedQueryImpl spec) (computation : OracleComp spec α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnotCompletable : ¬DeferredCompletable table context) :
    runSynchronizedResolved impl computation context fuel table cache = pure none := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      exact runSynchronizedResolved_pure_of_not_completable impl value context fuel table cache
        hnotCompletable
  | query_bind query next ih =>
      exact runSynchronizedResolved_query_bind_of_not_completable impl query next context fuel
        table cache hnotCompletable

set_option maxRecDepth 100000 in
theorem runSynchronizedResolved_bind
    (impl : ResolvedQueryImpl spec) (left : OracleComp spec α)
    (next : α → OracleComp spec β)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runSynchronizedResolved impl (left >>= next) context fuel table cache = (do
      let leftResult ← runSynchronizedResolved impl left context fuel table cache
      match leftResult with
      | none => pure none
      | some result =>
          runSynchronizedResolved impl (next result.value.1) result.context
            result.remaining result.table result.value.2) := by
  induction left using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value =>
      rw [pure_bind]
      by_cases hcompletable : DeferredCompletable table context
      · rw [runSynchronizedResolved_pure impl value context fuel table cache hcompletable]
        simp
      · rw [runSynchronizedResolved_pure_of_not_completable impl value context fuel table
          cache hcompletable,
          runSynchronizedResolved_of_not_completable impl (next value) context fuel table cache
            hcompletable]
        simp
  | query_bind query tail ih =>
      rw [bind_assoc, runSynchronizedResolved, OracleComp.construct_query_bind,
        runSynchronizedResolved, OracleComp.construct_query_bind]
      by_cases hcompletable : DeferredCompletable table context
      · simp only [dif_pos hcompletable, bind_assoc]
        apply bind_congr
        intro stepOption
        cases stepOption with
        | none => simp
        | some result =>
            exact ih result.value.1 result.context result.remaining result.table result.value.2
      · simp only [dif_neg hcompletable, pure_bind]

def SynchronizedResolvedImplCouples (table : OtsSecretIndex → HashOutput)
    (leftImpl rightImpl : ResolvedQueryImpl spec) : Prop :=
  ∀ query left right fuel leftCache rightCache,
    FinalizationContextEq table (some left) (some right) →
    left.state.values = right.state.values →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    left.state.revealed = right.state.revealed →
    RelTriple
      (leftImpl query left fuel table leftCache)
      (rightImpl query right fuel table rightCache)
      (FinalizationSynchronizedRunEq table)

set_option maxRecDepth 100000 in
theorem relTriple_runSynchronizedResolved
    {table : OtsSecretIndex → HashOutput}
    {leftImpl rightImpl : ResolvedQueryImpl spec}
    (himpl : SynchronizedResolvedImplCouples table leftImpl rightImpl)
    (computation : OracleComp spec α)
    (left right : DeferredContext) (fuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runSynchronizedResolved leftImpl computation left fuel table leftCache)
      (runSynchronizedResolved rightImpl computation right fuel table rightCache)
      (FinalizationSynchronizedRunEq table) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel leftCache
      rightCache with
  | pure value =>
      have hleftCompletable := hcontext.2.2.2
      have hrightCompletable : DeferredCompletable table right := by
        rcases hleftCompletable with ⟨completion, hcompletion⟩
        exact ⟨completion, (hcontext.1.deferredCompletion_iff completion).mp hcompletion⟩
      rw [runSynchronizedResolved_pure leftImpl value left fuel table leftCache
          hleftCompletable,
        runSynchronizedResolved_pure rightImpl value right fuel table rightCache
          hrightCompletable]
      apply relTriple_pure_pure
      left
      exact ⟨⟨rfl, hcontext, rfl, rfl, rfl, hcache, hrevealed⟩, hvalues⟩
  | query_bind query next ih =>
      have hleftCompletable := hcontext.2.2.2
      have hrightCompletable : DeferredCompletable table right := by
        rcases hleftCompletable with ⟨completion, hcompletion⟩
        exact ⟨completion, (hcontext.1.deferredCompletion_iff completion).mp hcompletion⟩
      rw [runSynchronizedResolved, OracleComp.construct_query_bind,
        runSynchronizedResolved, OracleComp.construct_query_bind]
      simp only [dif_pos hleftCompletable, dif_pos hrightCompletable]
      apply relTriple_bind
        (himpl query left right fuel leftCache rightCache hcontext hvalues hcache hrevealed)
      intro leftResult rightResult hrelation
      rcases hrelation with hclean | hdoomed
      · cases leftResult with
        | none =>
            cases rightResult with
            | none => simp [FinalizationSynchronizedRunEq, FinalizationMaterializedRunEq,
                MaterializedValuesEq]
            | some rightResult => simp [FinalizationMaterializedRunEq] at hclean
        | some leftResult =>
            cases rightResult with
            | none => simp [FinalizationMaterializedRunEq] at hclean
            | some rightResult =>
                rcases leftResult with ⟨leftContext, leftFuel, leftValue, leftTable⟩
                rcases rightResult with ⟨rightContext, rightFuel, rightValue, rightTable⟩
                rcases leftValue with ⟨leftOutput, nextLeftCache⟩
                rcases rightValue with ⟨rightOutput, nextRightCache⟩
                simp only [FinalizationMaterializedRunEq, MaterializedValuesEq] at hclean
                rcases hclean.1 with
                  ⟨houtput, hnextContext, hnextFuel, hleftTable, hrightTable,
                    hnextCache, hnextRevealed⟩
                subst rightOutput
                subst rightFuel
                subst leftTable
                subst rightTable
                exact ih leftOutput leftContext rightContext leftFuel nextLeftCache nextRightCache
                  hnextContext hclean.2 hnextCache hnextRevealed
      · cases leftResult with
        | none =>
            cases rightResult with
            | none => simp [FinalizationSynchronizedRunEq, FinalizationDoomedRun]
            | some rightResult =>
                have hrightTable := hdoomed.2.1
                have hrightNotCompletable :
                    ¬DeferredCompletable rightResult.table rightResult.context := by
                  rw [hrightTable]
                  exact hdoomed.2.2.2.2
                simp only
                change RelTriple (pure none)
                  (runSynchronizedResolved rightImpl (next rightResult.value.1)
                    rightResult.context rightResult.remaining rightResult.table
                    rightResult.value.2)
                  (FinalizationSynchronizedRunEq table)
                rw [runSynchronizedResolved_of_not_completable]
                · simp [FinalizationSynchronizedRunEq, FinalizationDoomedRun]
                · exact hrightNotCompletable
        | some leftResult =>
            cases rightResult with
            | none =>
                have hleftTable := hdoomed.1.1
                have hleftNotCompletable :
                    ¬DeferredCompletable leftResult.table leftResult.context := by
                  rw [hleftTable]
                  exact hdoomed.1.2.2.2
                simp only
                change RelTriple
                  (runSynchronizedResolved leftImpl (next leftResult.value.1)
                    leftResult.context leftResult.remaining leftResult.table leftResult.value.2)
                  (pure none) (FinalizationSynchronizedRunEq table)
                rw [runSynchronizedResolved_of_not_completable]
                · simp [FinalizationSynchronizedRunEq, FinalizationDoomedRun]
                · exact hleftNotCompletable
            | some rightResult =>
                have hleftTable := hdoomed.1.1
                have hrightTable := hdoomed.2.1
                have hleftNotCompletable :
                    ¬DeferredCompletable leftResult.table leftResult.context := by
                  rw [hleftTable]
                  exact hdoomed.1.2.2.2
                have hrightNotCompletable :
                    ¬DeferredCompletable rightResult.table rightResult.context := by
                  rw [hrightTable]
                  exact hdoomed.2.2.2.2
                simp only
                change RelTriple
                  (runSynchronizedResolved leftImpl (next leftResult.value.1)
                    leftResult.context leftResult.remaining leftResult.table leftResult.value.2)
                  (runSynchronizedResolved rightImpl (next rightResult.value.1)
                    rightResult.context rightResult.remaining rightResult.table
                    rightResult.value.2)
                  (FinalizationSynchronizedRunEq table)
                rw [runSynchronizedResolved_of_not_completable,
                  runSynchronizedResolved_of_not_completable]
                · simp [FinalizationSynchronizedRunEq, FinalizationDoomedRun]
                · exact hrightNotCompletable
                · exact hleftNotCompletable

theorem finalizationSynchronizedCouples_sequenceFin
    {table : OtsSecretIndex → HashOutput} {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ position,
      FinalizationSynchronizedCouples table (computation position)
        (computation position)) :
    FinalizationSynchronizedCouples table (sequenceFin computation)
      (sequenceFin computation) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using
        (finalizationSynchronizedCouples_pure table Fin.elim0 :
          FinalizationSynchronizedCouples table
            (pure Fin.elim0 : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) (Fin 0 → α))
            (pure Fin.elim0 : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) (Fin 0 → α)))
  | succ n ih =>
      rw [sequenceFin]
      apply (hcomponent 0).bind
      intro head
      apply (ih (fun position : Fin n => computation position.succ)
        (fun position => hcomponent position.succ)).bind
      intro tail
      exact finalizationSynchronizedCouples_pure table
        (Fin.cases head tail : Fin (n + 1) → α)

theorem finalizationSynchronizedCouples_ensureFullChain
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    FinalizationSynchronizedCouples table
      (ensureFullChain lay tree leafIdx chainIdx)
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  apply (finalizationSynchronizedCouples_sequenceFin
    (fun step : ChainStep =>
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step)))
    (fun step => finalizationSynchronizedCouples_ensureCoordinate table
      (.position (.chain lay tree leafIdx chainIdx step)))).bind
  intro _
  exact finalizationSynchronizedCouples_pure table ()

theorem finalizationSynchronizedCouples_ensureOtsLeaf
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    FinalizationSynchronizedCouples table (ensureOtsLeaf lay tree leafIdx)
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  apply (finalizationSynchronizedCouples_sequenceFin
    (fun chainIdx : ChainIndex => ensureFullChain lay tree leafIdx chainIdx)
    (fun chainIdx => finalizationSynchronizedCouples_ensureFullChain table lay tree leafIdx
      chainIdx)).bind
  intro _
  exact finalizationSynchronizedCouples_ensureCoordinate table
    (.position (.leaf lay tree leafIdx))

theorem finalizationSynchronizedCouples_ensureTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      FinalizationSynchronizedCouples table (ensureTreeNode lay tree level nodeIdx)
        (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx =>
      finalizationSynchronizedCouples_ensureOtsLeaf table lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      apply (finalizationSynchronizedCouples_ensureTreeNode table lay tree level
        (2 * nodeIdx)).bind
      intro _
      apply (finalizationSynchronizedCouples_ensureTreeNode table lay tree level
        (2 * nodeIdx + 1)).bind
      intro _
      by_cases hlevel : level < maxLayerHeight
      · rw [dif_pos hlevel]
        exact finalizationSynchronizedCouples_ensureCoordinate table
          (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
      · rw [dif_neg hlevel]
        exact finalizationSynchronizedCouples_pure table ()

theorem finalizationSynchronizedCouples_revealPublishedCoordinate
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) :
    FinalizationSynchronizedCouples table (revealPublishedCoordinate coordinate)
      (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (finalizationSynchronizedCouples_revealCoordinate table coordinate).bind fun value =>
    (finalizationSynchronizedCouples_publishCoordinate table coordinate).bind fun _ =>
      finalizationSynchronizedCouples_pure table value

set_option maxRecDepth 100000 in
theorem finalizationSynchronizedCouples_maskedPublishedTreeRoot
    (table : OtsSecretIndex → HashOutput) :
    FinalizationSynchronizedCouples table maskedPublishedTreeRoot
      maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  apply (finalizationSynchronizedCouples_ensureTreeNode table topLayer rootTree
    (layerHeight topLayer) 0).bind
  intro _
  exact finalizationSynchronizedCouples_revealPublishedCoordinate table
    (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))

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

noncomputable def canonicalDeferredAdversaryImpl
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
        runDeferredChronologicalSign parameter root table ftsSecret message context fuel cache >>=
          fun result => pure (canonicalizeResolvedRun table result)

def CanonicalReachableResolvedImplCouples (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (leftImpl : ResolvedQueryImpl spec)
    (rightImpl : QueryImpl spec (StateT (QueryCache HashSpec) ProbComp)) : Prop :=
  ∀ query context fuel cache concreteCache,
    ResolvedContextInvariant parameter table context
        (ordinaryQueryCache cache) concreteCache →
    VisibleResolvedComputationsCached parameter table context concreteCache →
    PublishedValues context.state →
    RelTriple
      (leftImpl query context fuel table cache)
      ((rightImpl query).run concreteCache)
      (ReachableResolvedRunRel parameter table)

set_option maxRecDepth 100000 in
theorem canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    CanonicalReachableResolvedImplCouples parameter table
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
      (unloggedMappedAdversaryImpl
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)) := by
  intro query context fuel cache concreteCache hinvariant hclosed hpublished
  cases query with
  | inl oracleQuery =>
      apply relTriple_canonicalizeResolvedRun_of_reachable parameter table
      exact reachableResolvedCouples_probingRomImpl parameter table oracleQuery context fuel cache
        concreteCache hinvariant hclosed hpublished
  | inr message =>
      apply relTriple_canonicalizeResolvedRun_of_reachable parameter table
      exact reachableResolvedCouples_maskedPublishedChronologicalSign_concrete parameter root
        table ftsSecret message context fuel cache concreteCache hinvariant hclosed hpublished

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

set_option maxRecDepth 100000 in
theorem revealedChainAllowed_canonicalChronologicalAdversaryQuery
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (targetCache : QueryCache HashSpec) (allowedLog : QueryLog SigningSpec)
    (completion : Coordinate → HashOutput) (fallback : QueryImpl HashSpec Id)
    (hlogRuns : ∀ (entry : (request : SignRequest) × SigningSpec.Range request)
      (signature : Signature), entry ∈ allowedLog → entry.2 = some signature →
        SuccessfulSignRun (tableAnswer parameter completion fallback) targetCache
          (⟨parameter, root,
            fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)
          entry.1 signature)
    (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult
      ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hallowed : RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        allowedLog)
      context.state)
    (hfragment : ∀ entry, entry ∈ signingLogFragment input result.value.1 →
      entry ∈ allowedLog)
    (hresult : some result ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
        input context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion)
    (hfallback : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback) :
    RevealedChainAllowed
      (CoveredChainCoordinate (tableAnswer parameter completion fallback) targetCache
        (⟨parameter, root,
          fun lay tree leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
          ftsSecret⟩ : SecretKey)
        allowedLog)
      result.context.state := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize,
    mem_support_bind_iff] at hresult
  obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
  cases rawOption with
  | none => simp [canonicalizeResolvedRun] at hcanonical
  | some rawResult =>
      simp only [canonicalizeResolvedRun, mem_support_pure_iff] at hcanonical
      have hresultEq : result =
          { rawResult with
            context := canonicalizeMaterializedValues table rawResult.context } :=
        Option.some.inj hcanonical
      subst result
      have hcore := resolvedCore_of_mem_runResolvedFromTable
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        context fuel table rawResult hinvariant.2.1.valuesConsistent hinvariant.2.2.1 hraw
      have hrawCompletion : DeferredCompletion table rawResult.context completion :=
        hcompletion.of_canonicalizeMaterializedValues hcore.2.1 hcore.2.2
      have hrawAllowed :=
        revealedChainAllowed_maskedChronologicalExpandedAdversaryQuery parameter root table
          ftsSecret targetCache allowedLog completion fallback hlogRuns input context fuel cache
            concreteCache rawResult hinvariant hclosed hpublished hallowed hfragment hraw
              hrawCompletion hfallback
      intro coordinate hchain hrevealed
      apply hrawAllowed coordinate hchain
      simpa [canonicalizeMaterializedValues] using hrevealed

theorem resolvedCore_of_mem_canonicalChronologicalAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult
      ((OracleWorld + SigningSpec).Range input × SplitHashCache))
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
        input context fuel table cache)) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize,
    mem_support_bind_iff] at hresult
  obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
  cases rawOption with
  | none => simp [canonicalizeResolvedRun] at hcanonical
  | some rawResult =>
      simp only [canonicalizeResolvedRun, mem_support_pure_iff] at hcanonical
      have hresultEq : result =
          { rawResult with
            context := canonicalizeMaterializedValues table rawResult.context } :=
        Option.some.inj hcanonical
      subst result
      have hcore := resolvedCore_of_mem_runResolvedFromTable
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        context fuel table rawResult hconsistent hstarts hraw
      exact ⟨hcore.1,
        canonicalizeMaterializedValues_valuesConsistent table rawResult.context hcore.2.1,
        canonicalizeMaterializedValues_startTableAgrees table rawResult.context⟩

theorem DeferredCompletion.of_mem_canonicalChronologicalAdversaryImpl
    {parameter : PublicParameter} {root : Digest}
    {table : OtsSecretIndex → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {input : (OracleWorld + SigningSpec).Domain}
    {context : DeferredContext} {fuel : Nat} {cache : SplitHashCache}
    {result : ResolvedRunResult
      ((OracleWorld + SigningSpec).Range input × SplitHashCache)}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret
        input context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion) :
    DeferredCompletion table context completion := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize,
    mem_support_bind_iff] at hresult
  obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
  cases rawOption with
  | none => simp [canonicalizeResolvedRun] at hcanonical
  | some rawResult =>
      simp only [canonicalizeResolvedRun, mem_support_pure_iff] at hcanonical
      have hresultEq : result =
          { rawResult with
            context := canonicalizeMaterializedValues table rawResult.context } :=
        Option.some.inj hcanonical
      subst result
      have hcore := resolvedCore_of_mem_runResolvedFromTable
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        context fuel table rawResult hconsistent hstarts hraw
      have hrawCompletion : DeferredCompletion table rawResult.context completion :=
        hcompletion.of_canonicalizeMaterializedValues hcore.2.1 hcore.2.2
      exact hrawCompletion.of_mem_runResolvedFromTable _ context fuel table rawResult completion
        hconsistent hstarts hraw

set_option maxRecDepth 100000 in
theorem DeferredCompletion.of_mem_runSynchronizedResolved_canonicalChronological
    {parameter : PublicParameter} {root : Digest}
    {table : OtsSecretIndex → HashOutput}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runSynchronizedResolved
        (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        computation context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion) :
    DeferredCompletion table context completion := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache result with
  | pure value =>
      by_cases hcompletable : DeferredCompletable table context
      · rw [runSynchronizedResolved_pure _ value context fuel table cache hcompletable] at hresult
        simp only [mem_support_pure_iff, Option.some.injEq] at hresult
        subst result
        exact hcompletion
      · rw [runSynchronizedResolved_pure_of_not_completable _ value context fuel table cache
          hcompletable] at hresult
        simp at hresult
  | query_bind input next ih =>
      rw [runSynchronizedResolved, OracleComp.construct_query_bind] at hresult
      by_cases hcompletable : DeferredCompletable table context
      · simp only [dif_pos hcompletable, mem_support_bind_iff] at hresult
        obtain ⟨stepOption, hstep, htail⟩ := hresult
        cases stepOption with
        | none => simp at htail
        | some stepResult =>
            have hstepCore :=
              resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table
                ftsSecret input context fuel cache stepResult hconsistent hstarts hstep
            change some result ∈ support
              (runSynchronizedResolved
                (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
                (next stepResult.value.1) stepResult.context stepResult.remaining
                  stepResult.table stepResult.value.2) at htail
            rw [hstepCore.1] at htail
            have hstepCompletion := ih stepResult.value.1 stepResult.context
              stepResult.remaining stepResult.value.2 result hstepCore.2.1 hstepCore.2.2 htail
                hcompletion
            exact hstepCompletion.of_mem_canonicalChronologicalAdversaryImpl hconsistent hstarts
              hstep
      · simp [hcompletable] at hresult

set_option maxRecDepth 100000 in
theorem resolvedCore_of_mem_runSynchronizedResolved_canonicalChronological
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runSynchronizedResolved
        (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        computation context fuel table cache)) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache result with
  | pure value =>
      by_cases hcompletable : DeferredCompletable table context
      · rw [runSynchronizedResolved_pure _ value context fuel table cache hcompletable] at hresult
        simp only [mem_support_pure_iff, Option.some.injEq] at hresult
        subst result
        exact ⟨rfl, hconsistent, hstarts⟩
      · rw [runSynchronizedResolved_pure_of_not_completable _ value context fuel table cache
          hcompletable] at hresult
        simp at hresult
  | query_bind input next ih =>
      rw [runSynchronizedResolved, OracleComp.construct_query_bind] at hresult
      by_cases hcompletable : DeferredCompletable table context
      · simp only [dif_pos hcompletable, mem_support_bind_iff] at hresult
        obtain ⟨stepOption, hstep, htail⟩ := hresult
        cases stepOption with
        | none => simp at htail
        | some stepResult =>
            have hstepCore :=
              resolvedCore_of_mem_canonicalChronologicalAdversaryImpl parameter root table
                ftsSecret input context fuel cache stepResult hconsistent hstarts hstep
            change some result ∈ support
              (runSynchronizedResolved
                (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
                (next stepResult.value.1) stepResult.context stepResult.remaining
                  stepResult.table stepResult.value.2) at htail
            rw [hstepCore.1] at htail
            exact ih stepResult.value.1 stepResult.context stepResult.remaining
              stepResult.value.2 result hstepCore.2.1 hstepCore.2.2 htail
      · simp [hcompletable] at hresult

set_option maxRecDepth 100000 in
theorem relTriple_runSynchronizedResolved_reachable
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {leftImpl : ResolvedQueryImpl spec}
    {rightImpl : QueryImpl spec (StateT (QueryCache HashSpec) ProbComp)}
    (himpl : CanonicalReachableResolvedImplCouples parameter table leftImpl rightImpl)
    (computation : OracleComp spec α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) :
    RelTriple
      (runSynchronizedResolved leftImpl computation context fuel table cache)
      ((simulateQ rightImpl computation).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache concreteCache
      with
  | pure value =>
      rw [runSynchronizedResolved_pure leftImpl value context fuel table cache
          hinvariant.2.2.2.1,
        simulateQ_pure]
      simp only [StateT.run_pure]
      exact relTriple_pure_pure
        (Or.inl ⟨rfl, rfl, hinvariant, hclosed, hpublished⟩)
  | query_bind query next ih =>
      rw [runSynchronizedResolved, OracleComp.construct_query_bind,
        simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, dif_pos hinvariant.2.2.2.1]
      apply relTriple_bind
        (himpl query context fuel cache concreteCache hinvariant hclosed hpublished)
      intro leftResult rightResult hrelation
      cases leftResult with
      | none =>
          have hbase := relTriple_true
            (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache))))
            ((simulateQ rightImpl (next rightResult.1)).run rightResult.2)
          have hsupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
              (fun finalLeft => finalLeft = none) (by
                intro finalLeft hsupport
                simpa using hsupport)
          apply relTriple_post_mono hsupported
          intro finalLeft _ hfinal
          rw [hfinal.2]
          trivial
      | some result =>
          rcases hrelation with hclean | hdoomed
          · rcases rightResult with ⟨rightValue, rightCache⟩
            have hvalue : result.value.1 = rightValue := hclean.2.1
            subst rightValue
            change RelTriple
              (runSynchronizedResolved leftImpl (next result.value.1) result.context
                result.remaining result.table result.value.2)
              ((simulateQ rightImpl (next result.value.1)).run rightCache)
              (ReachableResolvedRunRel parameter table)
            rw [hclean.1]
            exact ih result.value.1 result.context result.remaining result.value.2 rightCache
              hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
          · have hnotCompletable :
                ¬DeferredCompletable result.table result.context := by
              rw [hdoomed.1]
              exact hdoomed.2.2.2
            change RelTriple
              (runSynchronizedResolved leftImpl (next result.value.1) result.context
                result.remaining result.table result.value.2)
              ((simulateQ rightImpl (next rightResult.1)).run rightResult.2)
              (ReachableResolvedRunRel parameter table)
            rw [runSynchronizedResolved_of_not_completable leftImpl
              (next result.value.1) result.context result.remaining result.table result.value.2
              hnotCompletable]
            have hbase := relTriple_true
              (pure none : ProbComp (Option (ResolvedRunResult (α × SplitHashCache))))
              ((simulateQ rightImpl (next rightResult.1)).run rightResult.2)
            have hsupported :=
              SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
                (fun finalLeft => finalLeft = none) (by
                  intro finalLeft hsupport
                  simpa using hsupport)
            apply relTriple_post_mono hsupported
            intro finalLeft _ hfinal
            rw [hfinal.2]
            trivial

theorem concreteSupport_of_mem_runSynchronizedResolved
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {leftImpl : ResolvedQueryImpl spec}
    {rightImpl : QueryImpl spec (StateT (QueryCache HashSpec) ProbComp)}
    (himpl : CanonicalReachableResolvedImplCouples parameter table leftImpl rightImpl)
    (computation : OracleComp spec α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (result : ResolvedRunResult (α × SplitHashCache))
    (completion : Coordinate → HashOutput)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runSynchronizedResolved leftImpl computation context fuel table cache))
    (hcompletion : DeferredCompletion table result.context completion) :
    ∃ rightCache,
      ResolvedContextInvariant parameter table result.context
          (ordinaryQueryCache result.value.2) rightCache ∧
        VisibleResolvedComputationsCached parameter table result.context rightCache ∧
        PublishedValues result.context.state ∧
        (result.value.1, rightCache) ∈ support
          ((simulateQ rightImpl computation).run concreteCache) := by
  have hrel := relTriple_runSynchronizedResolved_reachable himpl computation context fuel cache
    concreteCache hinvariant hclosed hpublished
  obtain ⟨rightResult, hrightSupport, hrelation⟩ :=
    exists_right_of_relTriple_of_mem_support hrel hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  have hclean := hrelation.clean_of_completion hcompletion
  refine ⟨rightCache, hclean.2.1, hclean.2.2.1, hclean.2.2.2, ?_⟩
  rw [hclean.1]
  exact hrightSupport

theorem CacheAgreesWithFnOffTable.of_reachableRelTriple
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {leftRun : ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))}
    {rightRun : ProbComp (α × QueryCache HashSpec)}
    {context : DeferredContext} {cache concreteCache : QueryCache HashSpec}
    {result : ResolvedRunResult (α × SplitHashCache)}
    {completion : Coordinate → HashOutput} {fallback : QueryImpl HashSpec Id}
    (hrelation : RelTriple leftRun rightRun
      (ReachableResolvedRunRel parameter table))
    (hinvariant : ResolvedContextInvariant parameter table context cache concreteCache)
    (hresult : some result ∈ support leftRun)
    (hcompletion : DeferredCompletion table result.context completion)
    (hfinal : CacheAgreesWithFnOffTable parameter completion
      (ordinaryQueryCache result.value.2) fallback)
    (hrightLe : ∀ value finalCache,
      (value, finalCache) ∈ support rightRun → concreteCache ≤ finalCache) :
    CacheAgreesWithFnOffTable parameter completion cache fallback := by
  obtain ⟨rightResult, hrightSupport, hresultRelation⟩ :=
    exists_right_of_relTriple_of_mem_support hrelation hresult
  rcases rightResult with ⟨rightValue, rightCache⟩
  obtain ⟨_value, hfinalInvariant, _hfinalClosed, _hfinalPublished⟩ :=
    hresultRelation.clean_of_completion hcompletion
  intro input output hoff hcached
  have hconcrete : concreteCache input = some output :=
    hinvariant.2.2.2.2.1 input output hcached
  have hright : rightCache input = some output :=
    hrightLe rightValue rightCache hrightSupport hconcrete
  rcases hfinalInvariant.2.2.2.2.2 input output hright with hordinary | hfixed
  · exact hfinal input output hoff hordinary
  · rcases hfixed with ⟨position, hots, _hvalue, hinput⟩
    exact False.elim (hoff position hots (hinput completion hcompletion))


set_option maxRecDepth 100000 in
theorem synchronizedResolvedImplCouples_canonicalAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    SynchronizedResolvedImplCouples table
      (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
      (canonicalDeferredAdversaryImpl parameter root table ftsSecret) := by
  intro query left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
  cases query with
  | inl oracleQuery =>
      apply relTriple_bind
        (finalizationSynchronizedCouples_probingRomImpl table parameter oracleQuery
          left right fuel leftCache rightCache hcontext hvalues hcache hrevealed)
      intro leftResult rightResult hrelation
      apply relTriple_pure_pure
      exact finalizationSynchronizedRunEq_canonicalize table leftResult rightResult
        hrelation.toAdaptive
  | inr message =>
      exact relTriple_canonicalized_maskedPublishedChronologicalSign parameter root table
        ftsSecret message left right fuel leftCache rightCache hcontext hcache hrevealed

set_option maxRecDepth 100000 in
theorem relTriple_canonical_adversaryExecution
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (left right : DeferredContext) (fuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runSynchronizedResolved
        (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
        computation left fuel table leftCache)
      (runSynchronizedResolved
        (canonicalDeferredAdversaryImpl parameter root table ftsSecret)
        computation right fuel table rightCache)
      (FinalizationSynchronizedRunEq table) :=
  relTriple_runSynchronizedResolved
    (synchronizedResolvedImplCouples_canonicalAdversaryImpl parameter root table ftsSecret)
    computation left right fuel leftCache rightCache hcontext hvalues hcache hrevealed

noncomputable def canonicalVerifierFinish
    (parameter : PublicParameter) (root : Digest)
    (forgeryLog : Forgery × QueryLog SigningSpec) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) RetainedGameResult := do
  let verified ← simulateQ (probingRomImpl parameter)
    (scheme.verify ⟨root, parameter⟩ forgeryLog.1.message forgeryLog.1.signature)
  pure (root, (forgeryLog, verified))

noncomputable def concreteVerifierFinish
    (parameter : PublicParameter) (root : Digest)
    (forgeryLog : Forgery × QueryLog SigningSpec) :
    StateT (QueryCache HashSpec) ProbComp RetainedGameResult := do
  let verified ← simulateQ romImpl
    (scheme.verify ⟨root, parameter⟩ forgeryLog.1.message forgeryLog.1.signature)
  pure (root, (forgeryLog, verified))

theorem concreteVerifierFinish_cache_le
    (parameter : PublicParameter) (root : Digest)
    (forgeryLog : Forgery × QueryLog SigningSpec)
    (initialCache : QueryCache HashSpec)
    (result : RetainedGameResult × QueryCache HashSpec)
    (hresult : result ∈ support
      ((concreteVerifierFinish parameter root forgeryLog).run initialCache)) :
    initialCache ≤ result.2 := by
  unfold concreteVerifierFinish at hresult
  rw [StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨verifiedResult, hverified, hfinish⟩ := hresult
  simp only [StateT.run_pure, mem_support_pure_iff] at hfinish
  subst result
  exact simulateQ_romImpl_cache_le
    (scheme.verify ⟨root, parameter⟩ forgeryLog.1.message forgeryLog.1.signature)
    initialCache verifiedResult hverified

theorem reachableResolvedCouples_canonicalVerifierFinish
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (forgeryLog : Forgery × QueryLog SigningSpec) :
    ReachableResolvedCouples parameter table
      (canonicalVerifierFinish parameter root forgeryLog)
      (concreteVerifierFinish parameter root forgeryLog) := by
  unfold canonicalVerifierFinish concreteVerifierFinish
  apply (reachableResolvedCouples_probingRom parameter table
    (scheme.verify ⟨root, parameter⟩ forgeryLog.1.message
      forgeryLog.1.signature)).bind
  intro verified
  exact reachableResolvedCouples_pure parameter table (root, (forgeryLog, verified))

theorem finalizationSynchronizedCouples_canonicalVerifierFinish
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (forgeryLog : Forgery × QueryLog SigningSpec) :
    FinalizationSynchronizedCouples table
      (canonicalVerifierFinish parameter root forgeryLog)
      (canonicalVerifierFinish parameter root forgeryLog) := by
  unfold canonicalVerifierFinish
  apply (finalizationSynchronizedCouples_probingRom table parameter
    (scheme.verify ⟨root, parameter⟩ forgeryLog.1.message
      forgeryLog.1.signature)).bind
  intro verified
  exact finalizationSynchronizedCouples_pure table (root, (forgeryLog, verified))

noncomputable def canonicalVerifierContinuation
    (parameter : PublicParameter) (root : Digest)
    (result : Option (ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache))) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache))) :=
  match result with
  | none => pure none
  | some result =>
      runResolvedFromTable result.context result.remaining result.table
        ((canonicalVerifierFinish parameter root result.value.1).run result.value.2)

theorem relTriple_canonicalVerifierContinuation
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (left right : Option (ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache)))
    (hrelation : FinalizationSynchronizedRunEq table left right) :
    RelTriple
      (canonicalVerifierContinuation parameter root left)
      (canonicalVerifierContinuation parameter root right)
      (FinalizationSynchronizedRunEq table) := by
  rcases hrelation with hclean | hdoomed
  · cases left with
    | none =>
        cases right with
        | none => simp [canonicalVerifierContinuation, FinalizationSynchronizedRunEq,
            FinalizationMaterializedRunEq, MaterializedValuesEq]
        | some right => simp [FinalizationMaterializedRunEq] at hclean
    | some left =>
        cases right with
        | none => simp [FinalizationMaterializedRunEq] at hclean
        | some right =>
            rcases left with ⟨leftContext, leftFuel, leftValue, leftTable⟩
            rcases right with ⟨rightContext, rightFuel, rightValue, rightTable⟩
            rcases leftValue with ⟨leftOutput, leftCache⟩
            rcases rightValue with ⟨rightOutput, rightCache⟩
            simp only [FinalizationMaterializedRunEq, MaterializedValuesEq] at hclean
            rcases hclean.1 with
              ⟨houtput, hcontext, hfuel, hleftTable, hrightTable, hcache, hrevealed⟩
            subst rightOutput
            subst rightFuel
            subst leftTable
            subst rightTable
            exact finalizationSynchronizedCouples_canonicalVerifierFinish parameter root table
              leftOutput leftContext rightContext leftFuel leftCache rightCache hcontext
                hclean.2 hcache hrevealed
  · cases left with
    | none =>
        cases right with
        | none => simp [canonicalVerifierContinuation, FinalizationSynchronizedRunEq,
            FinalizationDoomedRun]
        | some right =>
            simp only [canonicalVerifierContinuation]
            rw [hdoomed.2.1]
            exact relTriple_pure_none_runResolvedFromTable_of_finalizationDoomed_synchronized
              table ((canonicalVerifierFinish parameter root right.value.1).run right.value.2)
                right.context right.remaining hdoomed.2.2
    | some left =>
        cases right with
        | none =>
            simp only [canonicalVerifierContinuation]
            rw [hdoomed.1.1]
            exact relTriple_runResolvedFromTable_pure_none_of_finalizationDoomed_synchronized
              table ((canonicalVerifierFinish parameter root left.value.1).run left.value.2)
                left.context left.remaining hdoomed.1.2
        | some right =>
            simp only [canonicalVerifierContinuation]
            rw [hdoomed.1.1, hdoomed.2.1]
            exact relTriple_runResolvedFromTable_of_finalizationDoomed_synchronized table
              ((canonicalVerifierFinish parameter root left.value.1).run left.value.2)
              ((canonicalVerifierFinish parameter root right.value.1).run right.value.2)
              left.context right.context left.remaining right.remaining hdoomed.1.2 hdoomed.2.2

theorem relTriple_canonicalVerifierContinuation_reachable
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (left : Option (ResolvedRunResult
      ((Forgery × QueryLog SigningSpec) × SplitHashCache)))
    (right : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hrelation : ReachableResolvedRunRel parameter table left right) :
    RelTriple
      (canonicalVerifierContinuation parameter root left)
      ((concreteVerifierFinish parameter root right.1).run right.2)
      (ReachableResolvedRunRel parameter table) := by
  cases left with
  | none =>
      have hbase := relTriple_true
        (pure none : ProbComp
          (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache))))
        ((concreteVerifierFinish parameter root right.1).run right.2)
      have hsupported :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun result => result = none) (by
            intro result hsupport
            simpa using hsupport)
      apply relTriple_post_mono hsupported
      intro result _ hsupport
      rw [hsupport.2]
      trivial
  | some result =>
      rcases hrelation with hclean | hdoomed
      · rcases right with ⟨rightValue, rightCache⟩
        have hvalue : result.value.1 = rightValue := hclean.2.1
        subst rightValue
        simp only [canonicalVerifierContinuation]
        rw [hclean.1]
        exact reachableResolvedCouples_canonicalVerifierFinish parameter root table
          result.value.1 result.context result.remaining result.value.2 rightCache
            hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
      · simp only [canonicalVerifierContinuation]
        rw [hdoomed.1]
        exact relTriple_runResolvedFromTable_of_doomed_reachable parameter table
          (canonicalVerifierFinish parameter root result.value.1)
          ((concreteVerifierFinish parameter root right.1).run right.2)
          result.context result.remaining result.value.2 hdoomed.2

noncomputable def canonicalChronologicalRetainedRunAfterFtsSecrets
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache))) := do
  let rootResult ← runResolvedFromTable
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure none
  | some rootResult => do
      let adversaryResult ← runSynchronizedResolved
        (canonicalChronologicalAdversaryImpl parameter rootResult.value.1 table ftsSecret)
        (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
        rootResult.context rootResult.remaining rootResult.table rootResult.value.2
      canonicalVerifierContinuation parameter rootResult.value.1 adversaryResult

noncomputable def canonicalDeferredRetainedRunAfterFtsSecrets
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache))) := do
  let rootResult ← runResolvedFromTable
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure none
  | some rootResult => do
      let adversaryResult ← runSynchronizedResolved
        (canonicalDeferredAdversaryImpl parameter rootResult.value.1 table ftsSecret)
        (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
        rootResult.context rootResult.remaining rootResult.table rootResult.value.2
      canonicalVerifierContinuation parameter rootResult.value.1 adversaryResult

set_option maxRecDepth 100000 in
theorem relTriple_canonicalChronologicalRest_reachable
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) :
    RelTriple
      (do
        let adversaryResult ← runSynchronizedResolved
          (canonicalChronologicalAdversaryImpl parameter root table ftsSecret)
          (signingTraceComputation (adversary.main ⟨root, parameter⟩))
          context fuel table cache
        canonicalVerifierContinuation parameter root adversaryResult)
      ((do
        let forgeryLog ← simulateQ
          (unloggedMappedAdversaryImpl
            (⟨parameter, root,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey))
          (signingTraceComputation (adversary.main ⟨root, parameter⟩))
        concreteVerifierFinish parameter root forgeryLog).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  rw [StateT.run_bind]
  apply relTriple_bind
    (relTriple_runSynchronizedResolved_reachable
      (canonicalReachableResolvedImplCouples_chronologicalAdversaryImpl parameter root table
        ftsSecret)
      (signingTraceComputation (adversary.main ⟨root, parameter⟩)) context fuel cache
        concreteCache hinvariant hclosed hpublished)
  intro left right hrelation
  exact relTriple_canonicalVerifierContinuation_reachable parameter root table left right
    hrelation

set_option maxRecDepth 100000 in
theorem relTriple_canonicalChronologicalRetainedRun_actual
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel)
      (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table))
      (ReachableResolvedRunRel parameter table) := by
  rw [← concreteRetainedGameAfterFtsSecrets_run_eq_actual adversary parameter table ftsSecret]
  unfold canonicalChronologicalRetainedRunAfterFtsSecrets
    concreteRetainedGameAfterFtsSecrets concreteRetainedPrefixAfterFtsSecrets
  simp only [StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  change RelTriple
    (runResolvedFromTable
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache) >>= fun rootOption =>
      match rootOption with
      | none => pure none
      | some rootResult => do
          let adversaryResult ← runSynchronizedResolved
            (canonicalChronologicalAdversaryImpl parameter rootResult.value.1 table ftsSecret)
            (signingTraceComputation
              (adversary.main ⟨rootResult.value.1, parameter⟩))
            rootResult.context rootResult.remaining rootResult.table rootResult.value.2
          canonicalVerifierContinuation parameter rootResult.value.1 adversaryResult)
    (((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter topLayer rootTree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨topLayer, rootTree, leafIdx, chainIdx⟩))
          (layerHeight topLayer) 0)).run ∅) >>= fun rootResult =>
      (do
        let forgeryLog ← simulateQ
          (unloggedMappedAdversaryImpl
            (⟨parameter, rootResult.1,
              fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
              ftsSecret⟩ : SecretKey))
          (signingTraceComputation (adversary.main ⟨rootResult.1, parameter⟩))
        concreteVerifierFinish parameter rootResult.1 forgeryLog).run rootResult.2)
    (ReachableResolvedRunRel parameter table)
  have hroot := reachableResolvedCouples_maskedPublishedTreeRoot parameter table
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel emptySplitHashCache ∅ (resolvedContextInvariant_empty parameter table)
      (visibleResolvedComputationsCached_empty parameter table emptyDeferredStructuralValues ∅)
      publishedValues_empty
  apply relTriple_bind hroot
  intro leftRoot rightRoot hrelation
  cases leftRoot with
  | none =>
      have hbase := relTriple_true
        (pure none : ProbComp
          (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache))))
        ((do
          let forgeryLog ← simulateQ
            (unloggedMappedAdversaryImpl
              (⟨parameter, rightRoot.1,
                fun lay tree leafIdx chainIdx =>
                  truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                ftsSecret⟩ : SecretKey))
            (signingTraceComputation (adversary.main ⟨rightRoot.1, parameter⟩))
          concreteVerifierFinish parameter rightRoot.1 forgeryLog).run rightRoot.2)
      have hsupported :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun result => result = none) (by
            intro result hsupport
            simpa using hsupport)
      apply relTriple_post_mono hsupported
      intro result _ hsupport
      rw [hsupport.2]
      trivial
  | some rootResult =>
      rcases hrelation with hclean | hdoomed
      · rcases rightRoot with ⟨rightRoot, rightCache⟩
        have hrootValue : rootResult.value.1 = rightRoot := hclean.2.1
        subst rightRoot
        simp only
        rw [hclean.1]
        exact relTriple_canonicalChronologicalRest_reachable adversary parameter
          rootResult.value.1 table ftsSecret rootResult.context rootResult.remaining
            rootResult.value.2 rightCache hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
      · have hnotCompletable :
            ¬DeferredCompletable rootResult.table rootResult.context := by
          rw [hdoomed.1]
          exact hdoomed.2.2.2
        simp only
        rw [runSynchronizedResolved_of_not_completable
          (canonicalChronologicalAdversaryImpl parameter rootResult.value.1 table ftsSecret)
          (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
          rootResult.context rootResult.remaining rootResult.table rootResult.value.2
          hnotCompletable]
        simp only [canonicalVerifierContinuation]
        have hbase := relTriple_true
          (pure none : ProbComp
            (Option (ResolvedRunResult (RetainedGameResult × SplitHashCache))))
          ((do
            let forgeryLog ← simulateQ
              (unloggedMappedAdversaryImpl
                (⟨parameter, rightRoot.1,
                  fun lay tree leafIdx chainIdx =>
                    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
                  ftsSecret⟩ : SecretKey))
              (signingTraceComputation (adversary.main ⟨rightRoot.1, parameter⟩))
            concreteVerifierFinish parameter rightRoot.1 forgeryLog).run rightRoot.2)
        have hsupported :=
          SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
            (fun result => result = none) (by
              intro result hsupport
              simpa using hsupport)
        apply relTriple_post_mono hsupported
        intro result _ hsupport
        rw [hsupport.2]
        trivial



theorem finalizationContextEq_empty (table : OtsSecretIndex → HashOutput) :
    FinalizationContextEq table
      (some
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues })
      (some
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }) := by
  let context : DeferredContext :=
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
  have hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output := by
    intro coordinate output _hvalue
    simp [context, LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
      LazyRevealProbe.State.empty]
  exact ⟨FinalizationViewEq.refl table context DeferredContext.valid_empty
      (startTableAgrees_empty table) hclean,
    DeferredContext.valid_empty, DeferredContext.valid_empty,
    deferredCompletable_empty table⟩

set_option maxRecDepth 100000 in
theorem relTriple_canonicalRetainedRunAfterFtsSecrets
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel)
      (canonicalDeferredRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel)
      (FinalizationSynchronizedRunEq table) := by
  unfold canonicalChronologicalRetainedRunAfterFtsSecrets
    canonicalDeferredRetainedRunAfterFtsSecrets
  let emptyContext : DeferredContext :=
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
  have hroot := finalizationSynchronizedCouples_maskedPublishedTreeRoot table
    emptyContext emptyContext fuel emptySplitHashCache emptySplitHashCache
      (finalizationContextEq_empty table) rfl rfl rfl
  apply relTriple_bind hroot
  intro leftRootResult rightRootResult hrootRelation
  rcases hrootRelation with hrootClean | hrootDoomed
  · cases leftRootResult with
    | none =>
        cases rightRootResult with
        | none => simp [FinalizationSynchronizedRunEq, FinalizationMaterializedRunEq,
            MaterializedValuesEq]
        | some right => simp [FinalizationMaterializedRunEq] at hrootClean
    | some leftRootResult =>
        cases rightRootResult with
        | none => simp [FinalizationMaterializedRunEq] at hrootClean
        | some rightRootResult =>
            rcases leftRootResult with
              ⟨leftContext, leftFuel, leftValue, leftTable⟩
            rcases rightRootResult with
              ⟨rightContext, rightFuel, rightValue, rightTable⟩
            rcases leftValue with ⟨leftRoot, leftCache⟩
            rcases rightValue with ⟨rightRoot, rightCache⟩
            simp only [FinalizationMaterializedRunEq, MaterializedValuesEq] at hrootClean
            rcases hrootClean.1 with
              ⟨hroot, hcontext, hfuel, hleftTable, hrightTable, hcache, hrevealed⟩
            subst rightRoot
            subst rightFuel
            subst leftTable
            subst rightTable
            apply relTriple_bind
              (relTriple_canonical_adversaryExecution parameter leftRoot table ftsSecret
                (signingTraceComputation (adversary.main ⟨leftRoot, parameter⟩))
                leftContext rightContext leftFuel leftCache rightCache hcontext hrootClean.2
                  hcache hrevealed)
            intro leftAdversaryResult rightAdversaryResult hadversary
            exact relTriple_canonicalVerifierContinuation parameter leftRoot table
              leftAdversaryResult rightAdversaryResult hadversary
  · cases leftRootResult with
    | none =>
        cases rightRootResult with
        | none => simp [FinalizationSynchronizedRunEq, FinalizationDoomedRun]
        | some rightRootResult =>
            have hrightTable := hrootDoomed.2.1
            have hrightNotCompletable :
                ¬DeferredCompletable rightRootResult.table rightRootResult.context := by
              rw [hrightTable]
              exact hrootDoomed.2.2.2.2
            simp only
            rw [runSynchronizedResolved_of_not_completable]
            · simp [canonicalVerifierContinuation, FinalizationSynchronizedRunEq,
                FinalizationDoomedRun]
            · exact hrightNotCompletable
    | some leftRootResult =>
        cases rightRootResult with
        | none =>
            have hleftTable := hrootDoomed.1.1
            have hleftNotCompletable :
                ¬DeferredCompletable leftRootResult.table leftRootResult.context := by
              rw [hleftTable]
              exact hrootDoomed.1.2.2.2
            simp only
            rw [runSynchronizedResolved_of_not_completable]
            · simp [canonicalVerifierContinuation, FinalizationSynchronizedRunEq,
                FinalizationDoomedRun]
            · exact hleftNotCompletable
        | some rightRootResult =>
            have hleftTable := hrootDoomed.1.1
            have hrightTable := hrootDoomed.2.1
            have hleftNotCompletable :
                ¬DeferredCompletable leftRootResult.table leftRootResult.context := by
              rw [hleftTable]
              exact hrootDoomed.1.2.2.2
            have hrightNotCompletable :
                ¬DeferredCompletable rightRootResult.table rightRootResult.context := by
              rw [hrightTable]
              exact hrootDoomed.2.2.2.2
            simp only
            rw [runSynchronizedResolved_of_not_completable,
              runSynchronizedResolved_of_not_completable]
            · simp [canonicalVerifierContinuation, FinalizationSynchronizedRunEq,
                FinalizationDoomedRun]
            · exact hrightNotCompletable
            · exact hleftNotCompletable

theorem relTriple_canonicalRetainedFinishIsNone
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    RelTriple
      (canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel
        >>= finishResolvedRunIsNone)
      (canonicalDeferredRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel >>=
        finishResolvedRunIsNone)
      (EqRel Bool) := by
  apply relTriple_bind
    (relTriple_canonicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel)
  intro left right hrelation
  exact relTriple_finishResolvedRunIsNone_of_finalizationAdaptiveRunEq table left right
    hrelation.toAdaptive

theorem prob_canonicalChronologicalRetainedFinishIsNone_eq_deferred
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= true |
        canonicalChronologicalRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel
          >>= finishResolvedRunIsNone] =
      Pr[= true |
        canonicalDeferredRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel >>=
          finishResolvedRunIsNone] :=
  probOutput_true_eq_of_relTriple_eqRel
    (relTriple_canonicalRetainedFinishIsNone adversary parameter table ftsSecret fuel)

def CanonicalFailureRefinementRunEq (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (α × SplitHashCache)) →
      Option (ResolvedRunResult (α × SplitHashCache)) → Prop :=
  fun left right =>
    (FinalizationMaterializedRunEq table left right ∧ CanonicalResolvedRun table right) ∨
      FinalizationDoomedRun table right

theorem canonicalFailureRefinementRunEq_canonicalize_right_of_synchronized
    (table : OtsSecretIndex → HashOutput)
    (left right : Option (ResolvedRunResult (α × SplitHashCache)))
    (hrelation : FinalizationSynchronizedRunEq table left right) :
    CanonicalFailureRefinementRunEq table left (canonicalizeResolvedRun table right) := by
  rcases hrelation with hclean | hdoomed
  · cases left with
    | none =>
        cases right with
        | none => exact Or.inl ⟨trivial, trivial⟩
        | some right => simp [FinalizationMaterializedRunEq] at hclean
    | some left =>
        cases right with
        | none => simp [FinalizationMaterializedRunEq] at hclean
        | some right =>
            rcases hclean.1 with
              ⟨hvalue, hcontext, hremaining, hleftTable, hrightTable, hcache, hrevealed⟩
            rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
            have hrightCanonicalView := finalizationViewEq_canonicalize_left table right.context
              hrightValid hview.rightStarts hview.rightClean
            have hrightCanonicalValid := canonicalizeMaterializedValues_valid table right.context
              hrightValid hview.rightClean
            left
            constructor
            · exact ⟨hvalue,
                ⟨hview.trans hrightCanonicalView.symm, hleftValid,
                  hrightCanonicalValid, hleftCompletable⟩,
                hremaining, hleftTable, hrightTable, hcache, by
                  simpa [canonicalizeResolvedRun,
                    canonicalizeMaterializedValues_revealed] using hrevealed⟩
            · exact canonicalizeMaterializedValues_canonical table right.context
                hrightValid.valuesConsistent
  · right
    cases right with
    | none => trivial
    | some right =>
        exact ⟨hdoomed.2.1,
          doomedResolvedContext_canonicalizeMaterializedValues hdoomed.2.2⟩

theorem relTriple_canonicalize_right_of_synchronized
    (table : OtsSecretIndex → HashOutput)
    (leftRun rightRun : ProbComp
      (Option (ResolvedRunResult (α × SplitHashCache))))
    (hrelation : RelTriple leftRun rightRun
      (FinalizationSynchronizedRunEq table)) :
    RelTriple leftRun
      (rightRun >>= fun result => pure (canonicalizeResolvedRun table result))
      (CanonicalFailureRefinementRunEq table) := by
  rw [← bind_pure leftRun]
  apply relTriple_bind hrelation
  intro left right hsync
  apply relTriple_pure_pure
  exact canonicalFailureRefinementRunEq_canonicalize_right_of_synchronized table left right
    hsync

def CanonicalRefinementResolvedImplCouples (table : OtsSecretIndex → HashOutput)
    (leftImpl rightImpl : ResolvedQueryImpl spec) : Prop :=
  ∀ query left right fuel leftCache rightCache,
    FinalizationContextEq table (some left) (some right) →
    CanonicalMaterializedValues table right →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    left.state.revealed = right.state.revealed →
    RelTriple
      (leftImpl query left fuel table leftCache)
      (rightImpl query right fuel table rightCache)
      (CanonicalFailureRefinementRunEq table)

set_option maxRecDepth 100000 in
theorem relTriple_runSynchronizedResolved_canonicalRefinement
    {table : OtsSecretIndex → HashOutput}
    {leftImpl rightImpl : ResolvedQueryImpl spec}
    (himpl : CanonicalRefinementResolvedImplCouples table leftImpl rightImpl)
    (computation : OracleComp spec α)
    (left right : DeferredContext) (fuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hrightCanonical : CanonicalMaterializedValues table right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed) :
    RelTriple
      (runSynchronizedResolved leftImpl computation left fuel table leftCache)
      (runSynchronizedResolved rightImpl computation right fuel table rightCache)
      (CanonicalFailureRefinementRunEq table) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel leftCache
      rightCache with
  | pure value =>
      have hleftCompletable := hcontext.2.2.2
      have hrightCompletable : DeferredCompletable table right := by
        rcases hleftCompletable with ⟨completion, hcompletion⟩
        exact ⟨completion, (hcontext.1.deferredCompletion_iff completion).mp hcompletion⟩
      rw [runSynchronizedResolved_pure leftImpl value left fuel table leftCache
          hleftCompletable,
        runSynchronizedResolved_pure rightImpl value right fuel table rightCache
          hrightCompletable]
      apply relTriple_pure_pure
      left
      exact ⟨⟨rfl, hcontext, rfl, rfl, rfl, hcache, hrevealed⟩,
        hrightCanonical⟩
  | query_bind query next ih =>
      have hleftCompletable := hcontext.2.2.2
      have hrightCompletable : DeferredCompletable table right := by
        rcases hleftCompletable with ⟨completion, hcompletion⟩
        exact ⟨completion, (hcontext.1.deferredCompletion_iff completion).mp hcompletion⟩
      rw [runSynchronizedResolved, OracleComp.construct_query_bind,
        runSynchronizedResolved, OracleComp.construct_query_bind]
      simp only [dif_pos hleftCompletable, dif_pos hrightCompletable]
      apply relTriple_bind
        (himpl query left right fuel leftCache rightCache hcontext hrightCanonical hcache
          hrevealed)
      intro leftResult rightResult hrelation
      rcases hrelation with hclean | hrightDoomed
      · cases leftResult with
        | none =>
            cases rightResult with
            | none => simp [CanonicalFailureRefinementRunEq, FinalizationMaterializedRunEq,
                CanonicalResolvedRun]
            | some rightResult => simp [FinalizationMaterializedRunEq] at hclean
        | some leftResult =>
            cases rightResult with
            | none => simp [FinalizationMaterializedRunEq] at hclean
            | some rightResult =>
                rcases leftResult with ⟨leftContext, leftFuel, leftValue, leftTable⟩
                rcases rightResult with ⟨rightContext, rightFuel, rightValue, rightTable⟩
                rcases leftValue with ⟨leftOutput, nextLeftCache⟩
                rcases rightValue with ⟨rightOutput, nextRightCache⟩
                simp only [FinalizationMaterializedRunEq, CanonicalResolvedRun] at hclean
                rcases hclean.1 with
                  ⟨houtput, hnextContext, hnextFuel, hleftTable, hrightTable,
                    hnextCache, hnextRevealed⟩
                subst rightOutput
                subst rightFuel
                subst leftTable
                subst rightTable
                exact ih leftOutput leftContext rightContext leftFuel nextLeftCache nextRightCache
                  hnextContext hclean.2 hnextCache hnextRevealed
      · have hbase := relTriple_true
            (match leftResult with
              | none => pure none
              | some result =>
                  runSynchronizedResolved leftImpl (next result.value.1) result.context
                    result.remaining result.table result.value.2)
            (match rightResult with
              | none => pure none
              | some result =>
                  runSynchronizedResolved rightImpl (next result.value.1) result.context
                    result.remaining result.table result.value.2)
        have hright :=
          SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
        apply relTriple_post_mono hright
        intro _ rightFinal hsupport
        right
        cases rightResult with
        | none =>
            have hnone : rightFinal = none := by simpa using hsupport.2
            subst rightFinal
            trivial
        | some rightResult =>
            have hrightTable := hrightDoomed.1
            have hnotCompletable :
                ¬DeferredCompletable rightResult.table rightResult.context := by
              rw [hrightTable]
              exact hrightDoomed.2.2.2
            have hrun := runSynchronizedResolved_of_not_completable rightImpl
              (next rightResult.value.1) rightResult.context rightResult.remaining
                rightResult.table rightResult.value.2 hnotCompletable
            have hnone : rightFinal = none := by
              simp only at hsupport
              rw [hrun] at hsupport
              simpa using hsupport.2
            subst rightFinal
            trivial

theorem relTriple_finishResolvedRunIsNone_of_canonicalFailureRefinement
    (table : OtsSecretIndex → HashOutput)
    (left right : Option (ResolvedRunResult (α × SplitHashCache)))
    (hrelation : CanonicalFailureRefinementRunEq table left right) :
    RelTriple (finishResolvedRunIsNone left) (finishResolvedRunIsNone right)
      (fun leftFailed rightFailed => leftFailed = true → rightFailed = true) := by
  rcases hrelation with hclean | hrightDoomed
  · apply relTriple_post_mono
      (relTriple_finishResolvedRunIsNone_of_finalizationMaterializedRunEq table left right
        hclean.1)
    intro leftFailed rightFailed heq hleft
    rw [← heq]
    exact hleft
  · cases right with
    | none =>
        have hright : finishResolvedRunIsNone
            (none : Option (ResolvedRunResult (α × SplitHashCache))) = pure true := by
          simp [finishResolvedRunIsNone, finishResolvedRun]
        rw [hright]
        have hbase := relTriple_true (finishResolvedRunIsNone left)
          (pure true : ProbComp Bool)
        have hsupported :=
          SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
        apply relTriple_post_mono hsupported
        intro leftFailed rightFailed hsupport _hleft
        simpa using hsupport.2
    | some right =>
        have hrightTable := hrightDoomed.1
        have hnotCompletable : ¬DeferredCompletable right.table right.context := by
          rw [hrightTable]
          exact hrightDoomed.2.2.2
        have hright : finishResolvedRunIsNone (some right) = pure true := by
          unfold finishResolvedRunIsNone
          rw [finishResolvedRun_of_not_deferredCompletable right hnotCompletable]
          simp
        rw [hright]
        have hbase := relTriple_true (finishResolvedRunIsNone left)
          (pure true : ProbComp Bool)
        have hsupported :=
          SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
        apply relTriple_post_mono hsupported
        intro leftFailed rightFailed hsupport _hleft
        simpa using hsupport.2

theorem prob_finishResolvedRunIsNone_le_of_canonicalFailureRefinement
    (table : OtsSecretIndex → HashOutput)
    (leftRun rightRun : ProbComp
      (Option (ResolvedRunResult (α × SplitHashCache))))
    (hrelation : RelTriple leftRun rightRun
      (CanonicalFailureRefinementRunEq table)) :
    Pr[= true | leftRun >>= finishResolvedRunIsNone] ≤
      Pr[= true | rightRun >>= finishResolvedRunIsNone] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_le_of_relTriple
    (p := fun failed : Bool => failed = true)
    (q := fun failed : Bool => failed = true)
    (relTriple_bind hrelation fun left right hresult =>
      relTriple_finishResolvedRunIsNone_of_canonicalFailureRefinement table left right hresult)
  intro leftFailed rightFailed himp hleft
  exact himp hleft

end SphincsSecurity.Concrete.OtsProbeSimulation
