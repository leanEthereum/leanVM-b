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

noncomputable def canonicalVerifierFinish
    (parameter : PublicParameter) (root : Digest)
    (forgeryLog : Forgery × QueryLog SigningSpec) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) RetainedGameResult := do
  let verified ← simulateQ (probingRomImpl parameter)
    (scheme.verify ⟨root, parameter⟩ forgeryLog.1.message forgeryLog.1.signature)
  pure (root, (forgeryLog, verified))

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

end SphincsSecurity.Concrete.OtsProbeSimulation
