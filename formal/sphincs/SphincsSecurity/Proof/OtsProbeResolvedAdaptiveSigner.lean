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

noncomputable def canonicalChronologicalAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ResolvedQueryImpl (OracleWorld + SigningSpec) :=
  fun query context fuel _table cache =>
    match query with
    | .inl oracleQuery =>
        runResolvedFromTable context fuel table
          ((probingRomImpl parameter oracleQuery).run cache)
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
          ((probingRomImpl parameter oracleQuery).run cache)
    | .inr message =>
        runDeferredChronologicalSign parameter root table ftsSecret message context fuel cache >>=
          fun result => pure (canonicalizeResolvedRun table result)

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
      exact finalizationSynchronizedCouples_probingRomImpl table parameter oracleQuery
        left right fuel leftCache rightCache hcontext hvalues hcache hrevealed
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

end SphincsSecurity.Concrete.OtsProbeSimulation
