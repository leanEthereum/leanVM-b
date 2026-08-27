import SphincsSecurity.Proof.OtsProbeRunSampling

/-!
# Dynamically resolved one-time structural values

Structural answers drawn before their proof-world reveal live in a separate partial table. The
lazy state therefore continues to hide them from `peek`, while a later reveal or finalization can
check every intervening probe against the already drawn answer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

abbrev DeferredStructuralValues := Position → Option HashOutput

def emptyDeferredStructuralValues : DeferredStructuralValues := fun _ => none

def DeferredStructuralValues.install (values : DeferredStructuralValues)
    (position : Position) (output : HashOutput) : DeferredStructuralValues :=
  Function.update values position (some output)

structure DeferredContext where
  state : LazyRevealProbe.State Coordinate
  values : DeferredStructuralValues

def DeferredContext.Valid (context : DeferredContext) : Prop :=
  (∀ position output,
      context.state.values (.position position) = some output →
        context.values position = some output) ∧
    ∀ coordinate output,
      context.state.values coordinate = some output →
        ¬context.state.hitAt coordinate output

def DeferredContext.ValuesConsistent (context : DeferredContext) : Prop :=
  ∀ position output,
    context.state.values (.position position) = some output →
      context.values position = some output

theorem DeferredContext.Valid.valuesConsistent {context : DeferredContext}
    (hvalid : context.Valid) : context.ValuesConsistent :=
  hvalid.1

theorem DeferredContext.ValuesConsistent.of_state_values_eq
    {left right : DeferredContext} (hconsistent : left.ValuesConsistent)
    (hstate : right.state.values = left.state.values)
    (hvalues : right.values = left.values) : right.ValuesConsistent := by
  intro position output hvalue
  rw [hvalues]
  apply hconsistent position output
  rw [← hstate]
  exact hvalue

theorem DeferredContext.ValuesConsistent.ensure
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (coordinate : Coordinate) :
    ({ context with state := context.state.ensure coordinate } : DeferredContext).ValuesConsistent :=
  hconsistent

theorem DeferredContext.ValuesConsistent.addPending
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (coordinate : Coordinate) (candidate : Digest) :
    ({ context with state := context.state.addPending coordinate candidate } :
      DeferredContext).ValuesConsistent :=
  hconsistent

theorem DeferredContext.ValuesConsistent.publish
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (coordinate : Coordinate) :
    ({ context with state := context.state.publish coordinate } : DeferredContext).ValuesConsistent :=
  hconsistent

def DeferredContext.positionValue (context : DeferredContext)
    (position : Position) : Option HashOutput :=
  match context.state.values (.position position) with
  | some output => some output
  | none => context.values position

structure DeferredResolution extends DeferredContext where
  output : HashOutput

noncomputable def resolveDeferredPositionValue (position : Position)
    (context : DeferredContext) : ProbComp (Option DeferredResolution) :=
  let coordinate := Coordinate.position position
  match context.state.values coordinate with
  | some output =>
      if context.state.hitAt coordinate output then
        pure none
      else
        pure (some (DeferredResolution.mk
          { state := context.state.clearPending coordinate,
            values := context.values.install position output }
          output))
  | none =>
      match context.values position with
      | some output =>
          if context.state.hitAt coordinate output then
            pure none
          else
            pure (some (DeferredResolution.mk
              { state := context.state.clearPending coordinate,
                values := context.values }
              output))
      | none => do
          let output ← LazyRevealProbe.sampleHashOutput
          if context.state.hitAt coordinate output then
            pure none
          else
            pure (some (DeferredResolution.mk
              { state := context.state.clearPending coordinate,
                values := context.values.install position output }
              output))

theorem resolveDeferredPositionValue_of_state_value
    (position : Position) (context : DeferredContext) (output : HashOutput)
    (hvalue : context.state.values (.position position) = some output) :
    resolveDeferredPositionValue position context =
      if context.state.hitAt (.position position) output then
        pure none
      else
        pure (some (DeferredResolution.mk
          { state := context.state.clearPending (.position position),
            values := context.values.install position output }
          output)) := by
  simp [resolveDeferredPositionValue, hvalue]

theorem resolveDeferredPositionValue_of_deferred_value
    (position : Position) (context : DeferredContext) (output : HashOutput)
    (hstate : context.state.values (.position position) = none)
    (hvalue : context.values position = some output) :
    resolveDeferredPositionValue position context =
      if context.state.hitAt (.position position) output then
        pure none
      else
        pure (some (DeferredResolution.mk
          { state := context.state.clearPending (.position position),
            values := context.values }
          output)) := by
  simp [resolveDeferredPositionValue, hstate, hvalue]

theorem resolveDeferredPositionValue_fresh
    (position : Position) (context : DeferredContext)
    (hstate : context.state.values (.position position) = none)
    (hvalue : context.values position = none) :
    resolveDeferredPositionValue position context = (do
      let output ← LazyRevealProbe.sampleHashOutput
      if context.state.hitAt (.position position) output then
        pure none
      else
        pure (some (DeferredResolution.mk
          { state := context.state.clearPending (.position position),
            values := context.values.install position output }
          output))) := by
  simp [resolveDeferredPositionValue, hstate, hvalue]

theorem resolveDeferredPositionValue_preserves_state_values
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.state.values = context.state.values := by
  unfold resolveDeferredPositionValue at hresult
  simp only at hresult
  cases hstate : context.state.values (.position position) with
  | some output =>
      rw [hstate] at hresult
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        rfl
  | none =>
      rw [hstate] at hresult
      cases hvalue : context.values position with
      | some output =>
          rw [hvalue] at hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hresult
          · simp [hhit] at hresult
            subst result
            rfl
      | none =>
          rw [hvalue, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hreturn⟩ := hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hreturn
          · simp [hhit] at hreturn
            subst result
            rfl

theorem resolveDeferredPositionValue_pending
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.state.pending = context.state.pendingAway (.position position) := by
  unfold resolveDeferredPositionValue at hresult
  simp only at hresult
  cases hstate : context.state.values (.position position) with
  | some output =>
      rw [hstate] at hresult
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        rfl
  | none =>
      rw [hstate] at hresult
      cases hvalue : context.values position with
      | some output =>
          rw [hvalue] at hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hresult
          · simp [hhit] at hresult
            subst result
            rfl
      | none =>
          rw [hvalue, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hreturn⟩ := hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hreturn
          · simp [hhit] at hreturn
            subst result
            rfl

theorem resolveDeferredPositionValue_not_hit
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    ¬context.state.hitAt (.position position) result.output := by
  unfold resolveDeferredPositionValue at hresult
  simp only at hresult
  cases hstate : context.state.values (.position position) with
  | some output =>
      rw [hstate] at hresult
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hhit
  | none =>
      rw [hstate] at hresult
      cases hvalue : context.values position with
      | some output =>
          rw [hvalue] at hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hresult
          · simp [hhit] at hresult
            subst result
            exact hhit
      | none =>
          rw [hvalue, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hreturn⟩ := hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hreturn
          · simp [hhit] at hreturn
            subst result
            exact hhit

theorem resolveDeferredPositionValue_installs
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.values position = some result.output := by
  unfold resolveDeferredPositionValue at hresult
  simp only at hresult
  cases hstate : context.state.values (.position position) with
  | some output =>
      rw [hstate] at hresult
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        simp [DeferredStructuralValues.install]
  | none =>
      rw [hstate] at hresult
      cases hvalue : context.values position with
      | some output =>
          rw [hvalue] at hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hresult
          · simp [hhit] at hresult
            subst result
            exact hvalue
      | none =>
          rw [hvalue, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hreturn⟩ := hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hreturn
          · simp [hhit] at hreturn
            subst result
            simp [DeferredStructuralValues.install]

theorem resolveDeferredPositionValue_preserves_other
    (position other : Position) (context : DeferredContext) (result : DeferredResolution)
    (hne : other ≠ position)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.values other = context.values other := by
  unfold resolveDeferredPositionValue at hresult
  simp only at hresult
  cases hstate : context.state.values (.position position) with
  | some output =>
      rw [hstate] at hresult
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        simp [DeferredStructuralValues.install, hne]
  | none =>
      rw [hstate] at hresult
      cases hvalue : context.values position with
      | some output =>
          rw [hvalue] at hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hresult
          · simp [hhit] at hresult
            subst result
            rfl
      | none =>
          rw [hvalue, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hreturn⟩ := hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hreturn
          · simp [hhit] at hreturn
            subst result
            simp [DeferredStructuralValues.install, hne]

theorem resolveDeferredPositionValue_resolves
    (position : Position) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.toDeferredContext.positionValue position = some result.output := by
  have hstateValues := resolveDeferredPositionValue_preserves_state_values
    position context result hresult
  cases hstate : context.state.values (.position position) with
  | some output =>
      unfold resolveDeferredPositionValue at hresult
      simp only [hstate] at hresult
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        simp [DeferredContext.positionValue, hstate]
  | none =>
      unfold DeferredContext.positionValue
      rw [hstateValues, hstate]
      exact resolveDeferredPositionValue_installs position context result hresult

theorem resolveDeferredPositionValue_preserves_positionValue
    (position other : Position) (context : DeferredContext) (result : DeferredResolution)
    (output : HashOutput)
    (hknown : context.positionValue other = some output)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.toDeferredContext.positionValue other = some output := by
  by_cases heq : other = position
  · subst other
    have hresolved := resolveDeferredPositionValue_resolves position context result hresult
    cases hstate : context.state.values (.position position) with
    | some cached =>
        have houtput : output = cached := by
          simpa [DeferredContext.positionValue, hstate] using hknown.symm
        unfold resolveDeferredPositionValue at hresult
        simp only [hstate] at hresult
        by_cases hhit : context.state.hitAt (.position position) cached
        · simp [hhit] at hresult
        · simp [hhit] at hresult
          subst result
          simpa [houtput]
    | none =>
        cases hvalue : context.values position with
        | some cached =>
            have houtput : output = cached := by
              simpa [DeferredContext.positionValue, hstate, hvalue] using hknown.symm
            unfold resolveDeferredPositionValue at hresult
            simp only [hstate, hvalue] at hresult
            by_cases hhit : context.state.hitAt (.position position) cached
            · simp [hhit] at hresult
            · simp [hhit] at hresult
              subst result
              simpa [houtput]
        | none => simp [DeferredContext.positionValue, hstate, hvalue] at hknown
  · have hstateValues := resolveDeferredPositionValue_preserves_state_values
      position context result hresult
    have hdeferred := resolveDeferredPositionValue_preserves_other
      position other context result heq hresult
    unfold DeferredContext.positionValue at hknown ⊢
    rw [hstateValues]
    cases hstate : context.state.values (.position other) with
    | some cached => simpa [hstate] using hknown
    | none => simpa [hstate, hdeferred] using hknown

def ResolveQueryRel (input : HashInput) (cache : QueryCache HashSpec) :
    Option DeferredResolution → HashOutput × QueryCache HashSpec → Prop
  | none, _ => True
  | some resolved, (output, finalCache) =>
      resolved.output = output ∧ finalCache = cache.cacheQuery input output

theorem relTriple_resolveDeferredPositionValue_freshQuery
    (position : Position) (context : DeferredContext) (input : HashInput)
    (cache : QueryCache HashSpec)
    (hstate : context.state.values (.position position) = none)
    (hvalue : context.values position = none) (hcache : cache input = none) :
    RelTriple
      (resolveDeferredPositionValue position context)
      ((randomOracle (spec := HashSpec) input).run cache)
      (ResolveQueryRel input cache) := by
  rw [resolveDeferredPositionValue_fresh position context hstate hvalue,
    QueryImpl.withCaching_run_none uniformSampleImpl hcache]
  unfold LazyRevealProbe.sampleHashOutput uniformSampleImpl
  simp only [map_eq_bind_pure_comp]
  apply relTriple_bind (relTriple_refl ($ᵗ HashOutput : ProbComp HashOutput))
  intro leftOutput rightOutput heq
  subst rightOutput
  by_cases hhit : context.state.hitAt (.position position) leftOutput
  · simp [hhit, ResolveQueryRel]
  · simp [hhit, ResolveQueryRel]

theorem relTriple_resolveDeferredPositionValue_cachedQuery
    (position : Position) (context : DeferredContext) (input : HashInput)
    (cache : QueryCache HashSpec) (output : HashOutput)
    (hknown : context.positionValue position = some output)
    (hcache : cache input = some output) :
    RelTriple
      (resolveDeferredPositionValue position context)
      ((randomOracle (spec := HashSpec) input).run cache)
      (ResolveQueryRel input cache) := by
  rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache]
  cases hstate : context.state.values (.position position) with
  | some cached =>
      have hcached : cached = output := by
        simpa [DeferredContext.positionValue, hstate] using hknown
      subst cached
      rw [resolveDeferredPositionValue_of_state_value position context output hstate]
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit, ResolveQueryRel]
      · have hcacheQuery : cache.cacheQuery input output = cache := by
          apply QueryCache.ext
          intro query
          by_cases hquery : query = input
          · subst query
            simp [QueryCache.cacheQuery_self, hcache]
          · simp [QueryCache.cacheQuery_of_ne cache output hquery]
        simp [hhit, ResolveQueryRel, hcacheQuery]
  | none =>
      cases hvalue : context.values position with
      | some cached =>
          have hcached : cached = output := by
            simpa [DeferredContext.positionValue, hstate, hvalue] using hknown
          subst cached
          rw [resolveDeferredPositionValue_of_deferred_value position context output hstate hvalue]
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit, ResolveQueryRel]
          · have hcacheQuery : cache.cacheQuery input output = cache := by
              apply QueryCache.ext
              intro query
              by_cases hquery : query = input
              · subst query
                simp [QueryCache.cacheQuery_self, hcache]
              · simp [QueryCache.cacheQuery_of_ne cache output hquery]
            simp [hhit, ResolveQueryRel, hcacheQuery]
      | none => simp [DeferredContext.positionValue, hstate, hvalue] at hknown

def ResolveInputAgrees (position : Position) (context : DeferredContext)
    (input : HashInput) (cache : QueryCache HashSpec) : Prop :=
  match context.positionValue position with
  | none => cache input = none
  | some output => cache input = some output

theorem relTriple_resolveDeferredPositionValue_of_inputAgrees
    (position : Position) (context : DeferredContext) (input : HashInput)
    (cache : QueryCache HashSpec)
    (hagrees : ResolveInputAgrees position context input cache) :
    RelTriple
      (resolveDeferredPositionValue position context)
      ((randomOracle (spec := HashSpec) input).run cache)
      (ResolveQueryRel input cache) := by
  unfold ResolveInputAgrees at hagrees
  cases hstate : context.state.values (.position position) with
  | some output =>
      have hknown : context.positionValue position = some output := by
        simp [DeferredContext.positionValue, hstate]
      rw [hknown] at hagrees
      exact relTriple_resolveDeferredPositionValue_cachedQuery position context input cache
        output hknown hagrees
  | none =>
      cases hvalue : context.values position with
      | some output =>
          have hknown : context.positionValue position = some output := by
            simp [DeferredContext.positionValue, hstate, hvalue]
          rw [hknown] at hagrees
          exact relTriple_resolveDeferredPositionValue_cachedQuery position context input cache
            output hknown hagrees
      | none =>
          have hmissing : context.positionValue position = none := by
            simp [DeferredContext.positionValue, hstate, hvalue]
          rw [hmissing] at hagrees
          exact relTriple_resolveDeferredPositionValue_freshQuery position context input cache
            hstate hvalue hagrees

noncomputable def resolveDeferredChainStart (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (context : DeferredContext) :
    Option DeferredResolution :=
  let coordinate := index.coordinate
  let output := table index
  match context.state.values coordinate with
  | some cached =>
      if context.state.hitAt coordinate cached then
        none
      else
        some (DeferredResolution.mk
          { state := context.state.clearPending coordinate,
            values := context.values }
          cached)
  | none =>
      if context.state.hitAt coordinate output then
        none
      else
        some (DeferredResolution.mk
          { state := context.state.clearPending coordinate,
            values := context.values }
          output)

theorem resolveDeferredChainStart_of_agrees
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (hagrees : StartTableAgrees context.state table)
    (hclean : ¬context.state.hitAt index.coordinate (table index)) :
    resolveDeferredChainStart table index context =
      some (DeferredResolution.mk
        { state := context.state.clearPending index.coordinate
          values := context.values }
        (table index)) := by
  unfold resolveDeferredChainStart
  cases hvalue : context.state.values index.coordinate with
  | none => simp [hvalue, hclean]
  | some output =>
      have hout : output = table index := hagrees index output hvalue
      subst output
      simp [hvalue, hclean]

theorem resolveDeferredChainStart_preserves_positionValue
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution) (position : Position)
    (output : HashOutput) (hknown : context.positionValue position = some output)
    (hresult : resolveDeferredChainStart table index context = some result) :
    result.toDeferredContext.positionValue position = some output := by
  unfold resolveDeferredChainStart at hresult
  dsimp only at hresult
  cases hvalue : context.state.values index.coordinate with
  | some cached =>
      rw [hvalue] at hresult
      by_cases hhit : context.state.hitAt index.coordinate cached
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        simpa [DeferredContext.positionValue, LazyRevealProbe.State.clearPending] using hknown
  | none =>
      rw [hvalue] at hresult
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        simpa [DeferredContext.positionValue, LazyRevealProbe.State.clearPending] using hknown

theorem resolveDeferredChainStart_output_of_agrees
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hagrees : StartTableAgrees context.state table)
    (hresult : resolveDeferredChainStart table index context = some result) :
    result.output = table index := by
  unfold resolveDeferredChainStart at hresult
  dsimp only at hresult
  cases hvalue : context.state.values index.coordinate with
  | some output =>
      have hout := hagrees index output hvalue
      rw [hvalue] at hresult
      by_cases hhit : context.state.hitAt index.coordinate output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hout
  | none =>
      rw [hvalue] at hresult
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        rfl

def ResolveChainRel
    (invariant : DeferredResolution → QueryCache HashSpec → Prop) :
    Option DeferredResolution → Digest × QueryCache HashSpec → Prop
  | none, _ => True
  | some resolved, (value, cache) =>
      value = truncateHash resolved.output ∧ invariant resolved cache

theorem relTriple_resolveDeferredChainStart
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (cache : QueryCache HashSpec)
    (invariant : DeferredResolution → QueryCache HashSpec → Prop)
    (hagrees : StartTableAgrees context.state table)
    (hpreserves : ∀ result,
      resolveDeferredChainStart table index context = some result →
      invariant result cache) :
    RelTriple
      (pure (resolveDeferredChainStart table index context) :
        ProbComp (Option DeferredResolution))
      (pure (truncateHash (table index), cache) : ProbComp (Digest × QueryCache HashSpec))
      (ResolveChainRel invariant) := by
  apply relTriple_pure_pure
  cases hresult : resolveDeferredChainStart table index context with
  | none => trivial
  | some result =>
      exact ⟨congrArg truncateHash
        (resolveDeferredChainStart_output_of_agrees table index context result hagrees hresult) |>.symm,
        hpreserves result hresult⟩

noncomputable def resolveDeferredChainPrefix
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    (steps : Nat) → steps ≤ chainLength - 1 → DeferredContext →
      ProbComp (Option DeferredResolution)
  | 0, _, context => pure (resolveDeferredChainStart table
      ⟨lay, tree, leafIdx, chainIdx⟩ context)
  | steps + 1, hsteps, context => do
      let previous ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps
        (by omega) context
      match previous with
      | none => pure none
      | some previous =>
          resolveDeferredPositionValue
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) previous.toDeferredContext

theorem resolveDeferredChainPrefix_preserves_state_values
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context result,
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      result.state.values = context.state.values
  | 0, hsteps, context, result, hresult => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      unfold resolveDeferredChainStart at hresult
      simp only [OtsSecretIndex.coordinate] at hresult
      cases hvalue : context.state.values
          (.chainStart lay tree leafIdx chainIdx) with
      | none =>
          simp only [hvalue] at hresult
          split at hresult <;> simp_all [LazyRevealProbe.State.clearPending]
      | some output =>
          simp only [hvalue] at hresult
          split at hresult <;> simp_all [LazyRevealProbe.State.clearPending]
  | steps + 1, hsteps, context, result, hresult => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previous, hprevious, hrest⟩ := hresult
      cases previous with
      | none => simp at hrest
      | some previous =>
          have hpreviousValues :=
            resolveDeferredChainPrefix_preserves_state_values table lay tree leafIdx chainIdx
              steps (by omega) context previous hprevious
          have hrestValues := resolveDeferredPositionValue_preserves_state_values
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
            previous.toDeferredContext result (by simpa using hrest)
          exact hrestValues.trans hpreviousValues

theorem resolveDeferredChainPrefix_installs_last
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (steps : Nat)
    (hsteps : steps + 1 ≤ chainLength - 1) (context : DeferredContext)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredChainPrefix table lay tree leafIdx chainIdx (steps + 1)
        hsteps context)) :
    result.values (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) =
      some result.output := by
  rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
  obtain ⟨previous, _hprevious, hrest⟩ := hresult
  cases previous with
  | none => simp at hrest
  | some previous =>
      exact resolveDeferredPositionValue_installs
        (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
        previous.toDeferredContext result (by simpa using hrest)

theorem resolveDeferredChainPrefix_resolves_last
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (steps : Nat)
    (hsteps : steps + 1 ≤ chainLength - 1) (context : DeferredContext)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredChainPrefix table lay tree leafIdx chainIdx (steps + 1)
        hsteps context)) :
    result.toDeferredContext.positionValue
        (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) = some result.output := by
  rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
  obtain ⟨previousOption, _hprevious, hrest⟩ := hresult
  cases previousOption with
  | none => simp at hrest
  | some previous =>
      exact resolveDeferredPositionValue_resolves
        (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
        previous.toDeferredContext result (by simpa using hrest)

def DeferredChainPrefixAvailable (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (steps : Nat)
    (context : DeferredContext) : Prop :=
  ∀ step : ChainStep, step.val < steps → ∃ output,
    context.positionValue (.chain lay tree leafIdx chainIdx step) = some output

theorem deferredChainPrefixAvailable_of_resolve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context result,
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      DeferredChainPrefixAvailable lay tree leafIdx chainIdx steps result.toDeferredContext
  | 0, hsteps, context, result, hresult => by
      intro step hlt
      omega
  | steps + 1, hsteps, context, result, hresult => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hpreviousAvailable := deferredChainPrefixAvailable_of_resolve
            table lay tree leafIdx chainIdx steps (by omega) context previous hprevious
          have hrest' : some result ∈ support
              (resolveDeferredPositionValue
                (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
                previous.toDeferredContext) := by
            simpa using hrest
          intro step hlt
          by_cases heq : step.val = steps
          · have hstep : step = ⟨steps, by omega⟩ := Fin.ext heq
            refine ⟨result.output, ?_⟩
            simpa [hstep] using resolveDeferredPositionValue_resolves
              (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
              previous.toDeferredContext result hrest'
          · have hbefore : step.val < steps := by omega
            obtain ⟨output, houtput⟩ := hpreviousAvailable step hbefore
            refine ⟨output, ?_⟩
            exact resolveDeferredPositionValue_preserves_positionValue
              (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
              (.chain lay tree leafIdx chainIdx step) previous.toDeferredContext result output
              houtput hrest'

theorem resolveDeferredChainPrefix_preserves_positionValue
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context result position output,
      context.positionValue position = some output →
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      result.toDeferredContext.positionValue position = some output
  | 0, hsteps, context, result, position, output, hknown, hresult => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      exact resolveDeferredChainStart_preserves_positionValue table
        ⟨lay, tree, leafIdx, chainIdx⟩ context result position output hknown hresult.symm
  | steps + 1, hsteps, context, result, position, output, hknown, hresult => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hmiddle := resolveDeferredChainPrefix_preserves_positionValue
            table lay tree leafIdx chainIdx steps (by omega) context previous position output
              hknown hprevious
          exact resolveDeferredPositionValue_preserves_positionValue
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) position
            previous.toDeferredContext result output hmiddle (by simpa using hrest)

theorem relTriple_resolveDeferredChainPrefix
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (context : DeferredContext) (cache : QueryCache HashSpec)
    (invariant : Nat → DeferredResolution → QueryCache HashSpec → Prop)
    (hagrees : StartTableAgrees context.state table)
    (hstartPreserves : ∀ result,
      resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context = some result →
      invariant 0 result cache)
    (hinput : ∀ steps (hsteps : steps < chainLength - 1) previous middleCache,
      invariant steps previous middleCache →
      ResolveInputAgrees (.chain lay tree leafIdx chainIdx ⟨steps, hsteps⟩)
        previous.toDeferredContext
        (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx ⟨steps, hsteps⟩)
          (digestBytes (truncateHash previous.output))) middleCache)
    (hqueryPreserves : ∀ steps (hsteps : steps < chainLength - 1) previous middleCache
        result output finalCache,
      invariant steps previous middleCache →
      some result ∈ support
        (resolveDeferredPositionValue
          (.chain lay tree leafIdx chainIdx ⟨steps, hsteps⟩) previous.toDeferredContext) →
      ResolveQueryRel
          (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx ⟨steps, hsteps⟩)
            (digestBytes (truncateHash previous.output))) middleCache
          (some result) (output, finalCache) →
      invariant (steps + 1) result finalCache) :
    ∀ steps hsteps,
      RelTriple
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context)
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (chainWalk parameter lay tree leafIdx chainIdx 0 steps
            (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))).run cache)
        (ResolveChainRel (invariant steps))
  | 0, hsteps => by
      simpa [resolveDeferredChainPrefix, chainWalk] using
        relTriple_resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩
          context cache (invariant 0) hagrees hstartPreserves
  | steps + 1, hsteps => by
      rw [resolveDeferredChainPrefix, chainWalk, simulateQ_bind, StateT.run_bind]
      apply relTriple_bind
        (relTriple_resolveDeferredChainPrefix parameter table lay tree leafIdx chainIdx context
          cache invariant hagrees hstartPreserves hinput hqueryPreserves steps (by omega))
      intro previous rightResult hprefix
      cases previous with
      | none =>
          have hbase := relTriple_true
            (pure (none : Option DeferredResolution) : ProbComp (Option DeferredResolution))
            ((simulateQ (randomOracle : QueryImpl HashSpec _)
              (if hstep : 0 + steps < chainLength - 1 then
                tweakableHash parameter
                  (.chain lay tree leafIdx chainIdx ⟨0 + steps, hstep⟩)
                  (digestBytes rightResult.1)
              else pure 0)).run rightResult.2)
          have hsupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
              (fun result => result = none) (by
                intro result hresult
                simpa using hresult)
          exact relTriple_post_mono hsupported (by
            intro leftResult _ hrelation
            rw [hrelation.2]
            trivial)
      | some previous =>
          rcases rightResult with ⟨previousValue, middleCache⟩
          rcases hprefix with ⟨hvalue, hinvariant⟩
          subst previousValue
          rw [dif_pos (show 0 + steps < chainLength - 1 by omega)]
          let step : ChainStep := ⟨steps, by omega⟩
          have hposition : (⟨0 + steps, by omega⟩ : ChainStep) = step := by
            apply Fin.ext
            simp [step]
          rw [hposition]
          unfold tweakableHash oracleHash
          rw [simulateQ_bind, StateT.run_bind]
          simp only [simulateQ_pure, StateT.run_pure]
          let input := tweakableHashInput parameter
            (.chain lay tree leafIdx chainIdx step) (digestBytes (truncateHash previous.output))
          have hagreesInput : ResolveInputAgrees
              (.chain lay tree leafIdx chainIdx step) previous.toDeferredContext input middleCache :=
            hinput steps (by omega) previous middleCache hinvariant
          have hquery := relTriple_resolveDeferredPositionValue_of_inputAgrees
            (.chain lay tree leafIdx chainIdx step) previous.toDeferredContext input middleCache
              hagreesInput
          have hbound : RelTriple
              (resolveDeferredPositionValue (.chain lay tree leafIdx chainIdx step)
              previous.toDeferredContext >>= fun resolved => pure resolved)
              ((randomOracle input).run middleCache >>= fun result =>
                pure (truncateHash result.1, result.2))
              (ResolveChainRel (invariant (steps + 1))) := by
            have hquerySupported :=
              SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hquery
                (fun resolved => resolved ∈ support
                  (resolveDeferredPositionValue
                    (.chain lay tree leafIdx chainIdx step) previous.toDeferredContext))
                (fun resolved hresolved => hresolved)
            apply relTriple_bind hquerySupported
            intro resolved queryResult hrelationSupported
            rcases hrelationSupported with ⟨hrelation, hresolvedSupport⟩
            apply relTriple_pure_pure
            cases resolved with
            | none => trivial
            | some resolved =>
                rcases queryResult with ⟨queryOutput, finalCache⟩
                refine ⟨?_, hqueryPreserves steps (by omega) previous middleCache resolved
                  queryOutput finalCache hinvariant hresolvedSupport hrelation⟩
                exact congrArg truncateHash hrelation.1 |>.symm
          simpa [step, input] using hbound

noncomputable def resolveDeferredChains
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : List ChainIndex → DeferredContext →
      ProbComp (Option DeferredContext)
  | [], context => pure (some context)
  | chainIdx :: remaining, context => do
      let resolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
        (chainLength - 1) (by omega) context
      match resolved with
      | none => pure none
      | some resolved =>
          resolveDeferredChains table lay tree leafIdx remaining resolved.toDeferredContext

theorem resolveDeferredChains_preserves_positionValue
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ chains context result position output,
      context.positionValue position = some output →
      some result ∈ support (resolveDeferredChains table lay tree leafIdx chains context) →
      result.positionValue position = some output
  | [], context, result, position, output, hknown, hresult => by
      simp [resolveDeferredChains] at hresult
      subst result
      exact hknown
  | chainIdx :: remaining, context, result, position, output, hknown, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          have hmiddle := resolveDeferredChainPrefix_preserves_positionValue
            table lay tree leafIdx chainIdx (chainLength - 1) (by omega) context resolved
              position output hknown hresolved
          exact resolveDeferredChains_preserves_positionValue table lay tree leafIdx remaining
            resolved.toDeferredContext result position output hmiddle (by simpa using hrest)

def DeferredChainsAvailable (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chains : List ChainIndex) (context : DeferredContext) : Prop :=
  ∀ chainIdx, chainIdx ∈ chains →
    DeferredChainPrefixAvailable lay tree leafIdx chainIdx (chainLength - 1) context

theorem deferredChainsAvailable_of_resolve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ chains context result,
      some result ∈ support (resolveDeferredChains table lay tree leafIdx chains context) →
      DeferredChainsAvailable lay tree leafIdx chains result
  | [], context, result, hresult => by
      intro chainIdx hmem
      simp at hmem
  | chainIdx :: remaining, context, result, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          have hhead := deferredChainPrefixAvailable_of_resolve table lay tree leafIdx chainIdx
            (chainLength - 1) (by omega) context resolved hresolved
          have htail := deferredChainsAvailable_of_resolve table lay tree leafIdx remaining
            resolved.toDeferredContext result (by simpa using hrest)
          intro other hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · subst other
            intro step hstep
            obtain ⟨output, houtput⟩ := hhead step hstep
            refine ⟨output, ?_⟩
            exact resolveDeferredChains_preserves_positionValue table lay tree leafIdx remaining
              resolved.toDeferredContext result
              (.chain lay tree leafIdx chainIdx step) output houtput (by simpa using hrest)
          · exact htail other hmem

noncomputable def resolveDeferredOtsLeaf
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) :
    ProbComp (Option DeferredResolution) := do
  let chains ← resolveDeferredChains table lay tree leafIdx
    (List.ofFn fun chainIdx : ChainIndex => chainIdx) context
  match chains with
  | none => pure none
  | some chains =>
      resolveDeferredPositionValue (.leaf lay tree leafIdx) chains

theorem resolveDeferredOtsLeaf_preserves_positionValue
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (result : DeferredResolution)
    (position : Position) (output : HashOutput)
    (hknown : context.positionValue position = some output)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    result.toDeferredContext.positionValue position = some output := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      have hmiddle := resolveDeferredChains_preserves_positionValue table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) context chains position output
          hknown hchains
      exact resolveDeferredPositionValue_preserves_positionValue
        (.leaf lay tree leafIdx) position chains result output hmiddle (by simpa using hrest)

theorem resolveDeferredOtsLeaf_resolves
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    result.toDeferredContext.positionValue (.leaf lay tree leafIdx) = some result.output := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, _hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      exact resolveDeferredPositionValue_resolves (.leaf lay tree leafIdx) chains result
        (by simpa using hrest)

def DeferredOtsLeafChildrenAvailable (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) : Prop :=
  ∀ chainIdx : ChainIndex, ∃ output,
    context.positionValue
      (.chain lay tree leafIdx chainIdx Position.lastChainStep) = some output

theorem deferredOtsLeafChildrenAvailable_of_resolve
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    DeferredOtsLeafChildrenAvailable lay tree leafIdx result.toDeferredContext := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      have havailable := deferredChainsAvailable_of_resolve table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) context chains hchains
      intro chainIdx
      have hmem : chainIdx ∈ List.ofFn (fun chainIdx : ChainIndex => chainIdx) := by
        simp only [List.mem_ofFn]
        exact ⟨chainIdx, rfl⟩
      obtain ⟨output, houtput⟩ := havailable chainIdx hmem Position.lastChainStep (by
        simp [Position.lastChainStep, chainLength, winternitzBits])
      refine ⟨output, ?_⟩
      exact resolveDeferredPositionValue_preserves_positionValue (.leaf lay tree leafIdx)
        (.chain lay tree leafIdx chainIdx Position.lastChainStep) chains result output houtput
          (by simpa using hrest)

noncomputable def resolveDeferredTreeNode
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    (level nodeIdx : Nat) → level ≤ maxLayerHeight → DeferredContext →
      ProbComp (Option DeferredResolution)
  | 0, nodeIdx, _, context =>
      resolveDeferredOtsLeaf table lay tree (leafOfNat nodeIdx) context
  | level + 1, nodeIdx, hlevel, context => do
      let left ← resolveDeferredTreeNode table lay tree level (2 * nodeIdx) (by omega) context
      match left with
      | none => pure none
      | some left => do
          let right ← resolveDeferredTreeNode table lay tree level (2 * nodeIdx + 1)
            (by omega) left.toDeferredContext
          match right with
          | none => pure none
          | some right =>
              resolveDeferredPositionValue
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
                right.toDeferredContext

def deferredTreePosition (lay : Layer) (tree : TreeIndex) :
    (level nodeIdx : Nat) → level ≤ maxLayerHeight → Position
  | 0, nodeIdx, _ => .leaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx, hlevel =>
      .node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)

theorem resolveDeferredTreeNode_preserves_positionValue
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel context result position output,
      context.positionValue position = some output →
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      result.toDeferredContext.positionValue position = some output
  | 0, nodeIdx, hlevel, context, result, position, output, hknown, hresult =>
      resolveDeferredOtsLeaf_preserves_positionValue table lay tree (leafOfNat nodeIdx)
        context result position output hknown hresult
  | level + 1, nodeIdx, hlevel, context, result, position, output, hknown, hresult => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hleftKnown := resolveDeferredTreeNode_preserves_positionValue table lay tree
                level (2 * nodeIdx) (by omega) context left position output hknown hleft
              have hrightKnown := resolveDeferredTreeNode_preserves_positionValue table lay tree
                level (2 * nodeIdx + 1) (by omega) left.toDeferredContext right position output
                  hleftKnown hright
              exact resolveDeferredPositionValue_preserves_positionValue
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) position
                right.toDeferredContext result output hrightKnown (by simpa using hafterRight)

theorem resolveDeferredTreeNode_resolves
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel context result,
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      result.toDeferredContext.positionValue
        (deferredTreePosition lay tree level nodeIdx hlevel) = some result.output
  | 0, nodeIdx, hlevel, context, result, hresult =>
      resolveDeferredOtsLeaf_resolves table lay tree (leafOfNat nodeIdx) context result hresult
  | level + 1, nodeIdx, hlevel, context, result, hresult => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, _hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, _hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              simpa [deferredTreePosition] using resolveDeferredPositionValue_resolves
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
                right.toDeferredContext result (by simpa using hafterRight)

theorem resolveDeferredTreeNode_children_available
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (hlevel : level + 1 ≤ maxLayerHeight)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredTreeNode table lay tree (level + 1) nodeIdx hlevel context)) :
    (∃ output, result.toDeferredContext.positionValue
        (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)) = some output) ∧
      (∃ output, result.toDeferredContext.positionValue
        (deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega)) = some output) := by
  rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
  obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
  cases leftOption with
  | none => simp at hafterLeft
  | some left =>
      rw [mem_support_bind_iff] at hafterLeft
      obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
      cases rightOption with
      | none => simp at hafterRight
      | some right =>
          have hleftValue := resolveDeferredTreeNode_resolves table lay tree level
            (2 * nodeIdx) (by omega) context left hleft
          have hleftInRight := resolveDeferredTreeNode_preserves_positionValue table lay tree level
            (2 * nodeIdx + 1) (by omega) left.toDeferredContext right
              (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)) left.output
              hleftValue hright
          have hrightValue := resolveDeferredTreeNode_resolves table lay tree level
            (2 * nodeIdx + 1) (by omega) left.toDeferredContext right hright
          have hfinalLeft := resolveDeferredPositionValue_preserves_positionValue
            (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
            (deferredTreePosition lay tree level (2 * nodeIdx) (by omega))
            right.toDeferredContext result left.output hleftInRight (by simpa using hafterRight)
          have hfinalRight := resolveDeferredPositionValue_preserves_positionValue
            (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
            (deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega))
            right.toDeferredContext result right.output hrightValue (by simpa using hafterRight)
          exact ⟨⟨left.output, hfinalLeft⟩, ⟨right.output, hfinalRight⟩⟩

noncomputable def resolveDeferredPosition
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) : ProbComp (Option DeferredResolution) :=
  match position with
  | .chain lay tree leafIdx chainIdx step =>
      resolveDeferredChainPrefix table lay tree leafIdx chainIdx (step.val + 1)
        (by have := step.isLt; omega) context
  | .leaf lay tree leafIdx => resolveDeferredOtsLeaf table lay tree leafIdx context
  | .node lay tree level nodeIdx =>
      resolveDeferredTreeNode table lay tree (level.val + 1) nodeIdx
        (by have := level.isLt; omega) context
  | position => resolveDeferredPositionValue position context

def ResolvableOtsPosition : Position → Prop
  | .chain _ _ _ _ _ => True
  | .leaf _ _ _ => True
  | .node _ _ level nodeIdx =>
      2 ^ (level.val + 1) * (nodeIdx.val + 1) ≤ 2 ^ maxLayerHeight
  | _ => False

noncomputable def resolveDeferredReveal
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) : ProbComp (Option DeferredResolution) := by
  classical
  exact if ResolvableOtsPosition position then
      resolveDeferredPosition table position context
    else
      resolveDeferredPositionValue position context

theorem resolveDeferredPosition_preserves_positionValue
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (position : Position) (output : HashOutput)
    (hknown : context.positionValue position = some output)
    (hresult : some result ∈ support
      (resolveDeferredPosition table target context)) :
    result.toDeferredContext.positionValue position = some output := by
  cases target with
  | chain lay tree leafIdx chainIdx step =>
      exact resolveDeferredChainPrefix_preserves_positionValue table lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) context result position output hknown hresult
  | leaf lay tree leafIdx =>
      exact resolveDeferredOtsLeaf_preserves_positionValue table lay tree leafIdx context result
        position output hknown hresult
  | node lay tree level nodeIdx =>
      exact resolveDeferredTreeNode_preserves_positionValue table lay tree (level.val + 1)
        nodeIdx (by have := level.isLt; omega) context result position output hknown hresult
  | ftsLeaf index tree leafIdx =>
      exact resolveDeferredPositionValue_preserves_positionValue (.ftsLeaf index tree leafIdx)
        position context result output hknown hresult
  | ftsNode index tree level nodeIdx =>
      exact resolveDeferredPositionValue_preserves_positionValue (.ftsNode index tree level nodeIdx)
        position context result output hknown hresult
  | ftsRoots index =>
      exact resolveDeferredPositionValue_preserves_positionValue (.ftsRoots index)
        position context result output hknown hresult

theorem resolveDeferredPosition_resolves
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    result.toDeferredContext.positionValue position = some result.output := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      simpa using resolveDeferredChainPrefix_resolves_last table lay tree leafIdx chainIdx
        step.val (by have := step.isLt; omega) context result hresult
  | leaf lay tree leafIdx =>
      exact resolveDeferredOtsLeaf_resolves table lay tree leafIdx context result hresult
  | node lay tree level nodeIdx =>
      have hleaf : leafOfNat nodeIdx.val = nodeIdx := leafOfNat_val nodeIdx
      simpa [deferredTreePosition, hleaf] using resolveDeferredTreeNode_resolves table lay tree
        (level.val + 1) nodeIdx (by have := level.isLt; omega) context result hresult
  | ftsLeaf index tree leafIdx =>
      exact resolveDeferredPositionValue_resolves (.ftsLeaf index tree leafIdx) context result hresult
  | ftsNode index tree level nodeIdx =>
      exact resolveDeferredPositionValue_resolves (.ftsNode index tree level nodeIdx) context result
        hresult
  | ftsRoots index =>
      exact resolveDeferredPositionValue_resolves (.ftsRoots index) context result hresult

structure ResolvedRunResult (alpha : Type) where
  context : DeferredContext
  remaining : Nat
  value : alpha
  table : OtsSecretIndex → HashOutput

noncomputable def runResolvedFromTable
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (Option (ResolvedRunResult alpha)) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) alpha =>
      DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        ProbComp (Option (ResolvedRunResult alpha)))
    (fun value context remaining table =>
      pure (some ⟨context, remaining, value, table⟩))
    (fun input _next recursivelyRun context fuel table =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output context fuel table
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          recursivelyRun output context fuel table
      | .ensure coordinate =>
          recursivelyRun ()
            { context with state := context.state.ensure coordinate } fuel table
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure none
          | remaining + 1 =>
              if coordinate ∈ context.state.revealed then
                recursivelyRun () context remaining table
              else
                recursivelyRun ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining table
      | .peek coordinate =>
          recursivelyRun (context.state.values coordinate) context fuel table
      | .publish coordinate =>
          recursivelyRun ()
            { context with state := context.state.publish coordinate } fuel table
      | .reveal coordinate => do
          let resolved ← match coordinate with
            | .chainStart lay tree leafIdx chainIdx =>
                pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context)
            | .position position => resolveDeferredReveal table position context
          match resolved with
          | none => pure none
          | some resolved =>
              recursivelyRun resolved.output
                { state := context.state.materialize coordinate resolved.output
                  values := resolved.values }
                fuel table)
    computation context fuel table

theorem runResolvedFromTable_uniform_query_bind
    (context : DeferredContext) (fuel n : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runResolvedFromTable context fuel table (next output)) := by
  rw [runResolvedFromTable, OracleComp.construct_query_bind]
  rfl

theorem runResolvedFromTable_hashOutput_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runResolvedFromTable context fuel table (next output)) := by
  rw [runResolvedFromTable, OracleComp.construct_query_bind]
  rfl

theorem runResolvedFromTable_ensure_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runResolvedFromTable
        { context with state := context.state.ensure coordinate } fuel table (next ()) := by
  rw [runResolvedFromTable, OracleComp.construct_query_bind]
  rfl

theorem runResolvedFromTable_probe_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runResolvedFromTable context remaining table (next ())
          else
            runResolvedFromTable
              { context with state := context.state.addPending coordinate candidate }
              remaining table (next ()) := by
  rw [runResolvedFromTable, OracleComp.construct_query_bind]
  rfl

theorem runResolvedFromTable_peek_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runResolvedFromTable context fuel table
        (next (context.state.values coordinate)) := by
  rw [runResolvedFromTable, OracleComp.construct_query_bind]
  rfl

theorem runResolvedFromTable_publish_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runResolvedFromTable
        { context with state := context.state.publish coordinate } fuel table (next ()) := by
  rw [runResolvedFromTable, OracleComp.construct_query_bind]
  rfl

theorem runResolvedFromTable_reveal_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let resolved ← match coordinate with
        | .chainStart lay tree leafIdx chainIdx =>
            pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context)
        | .position position => resolveDeferredReveal table position context
      match resolved with
      | none => pure none
      | some resolved =>
          runResolvedFromTable
            { state := context.state.materialize coordinate resolved.output
              values := resolved.values }
            fuel table (next resolved.output)) := by
  cases coordinate <;> rw [runResolvedFromTable, OracleComp.construct_query_bind] <;> rfl

theorem runResolvedFromTable_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (left : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (next : alpha → OracleComp (LazyRevealProbe.World Coordinate) beta) :
    runResolvedFromTable context fuel table (left >>= next) =
      runResolvedFromTable context fuel table left >>= fun result =>
        match result with
        | none => pure none
        | some result =>
            runResolvedFromTable result.context result.remaining result.table
              (next result.value) := by
  induction left using OracleComp.inductionOn generalizing context fuel with
  | pure value => simp [runResolvedFromTable]
  | query_bind input continuation ih =>
      cases input with
      | uniform n =>
          rw [bind_assoc, runResolvedFromTable_uniform_query_bind,
            runResolvedFromTable_uniform_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output context fuel
      | hashOutput =>
          rw [bind_assoc, runResolvedFromTable_hashOutput_query_bind,
            runResolvedFromTable_hashOutput_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output context fuel
      | ensure coordinate =>
          rw [bind_assoc, runResolvedFromTable_ensure_query_bind,
            runResolvedFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel
      | probe coordinate candidate =>
          rw [bind_assoc, runResolvedFromTable_probe_query_bind,
            runResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining
      | peek coordinate =>
          rw [bind_assoc, runResolvedFromTable_peek_query_bind,
            runResolvedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [bind_assoc, runResolvedFromTable_publish_query_bind,
            runResolvedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
      | reveal coordinate =>
          rw [bind_assoc, runResolvedFromTable_reveal_query_bind,
            runResolvedFromTable_reveal_query_bind]
          cases coordinate <;> simp only [bind_assoc]
          all_goals
            apply bind_congr
            intro resolved
            cases resolved with
            | none => simp
            | some resolved =>
                exact ih resolved.output
                  { state := context.state.materialize _ resolved.output
                    values := resolved.values }
                  fuel

theorem runResolvedFromTable_revealCoordinate
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (cache : SplitHashCache) :
    runResolvedFromTable context fuel table
        ((revealCoordinate coordinate).run cache) = (do
      let resolved ← match coordinate with
        | .chainStart lay tree leafIdx chainIdx =>
            pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context)
        | .position position => resolveDeferredReveal table position context
      match resolved with
      | none => pure none
      | some resolved =>
          pure (some ⟨
            { state := context.state.materialize coordinate resolved.output
              values := resolved.values },
            fuel,
            (truncateHash resolved.output,
              Function.update cache (.hidden coordinate) (some resolved.output)),
            table⟩)) := by
  rw [revealCoordinate_run, LazyRevealProbe.revealQuery,
    runResolvedFromTable_reveal_query_bind]
  cases coordinate <;> simp [runResolvedFromTable]

theorem value_ne_none_of_mem_runResolvedFromTable_revealCoordinate
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (cache : SplitHashCache) (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table ((revealCoordinate coordinate).run cache))) :
    result.context.state.values coordinate ≠ none := by
  rw [runResolvedFromTable_revealCoordinate] at hresult
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      cases hresolve : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp [hresolve] at hresult
      | some resolved =>
          simp [hresolve] at hresult
          subst result
          simp [LazyRevealProbe.State.materialize]
  | position position =>
      rw [mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          simp at hrest
          subst result
          simp [LazyRevealProbe.State.materialize]

theorem runResolvedFromTable_revealCoordinateOutput
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (cache : SplitHashCache) :
    runResolvedFromTable context fuel table
        ((revealCoordinateOutput coordinate).run cache) = (do
      let resolved ← match coordinate with
        | .chainStart lay tree leafIdx chainIdx =>
            pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context)
        | .position position => resolveDeferredReveal table position context
      match resolved with
      | none => pure none
      | some resolved =>
          pure (some ⟨
            { state := context.state.materialize coordinate resolved.output
              values := resolved.values },
            fuel,
            (resolved.output,
              Function.update cache (.hidden coordinate) (some resolved.output)),
            table⟩)) := by
  rw [revealCoordinateOutput_run, LazyRevealProbe.revealQuery,
    runResolvedFromTable_reveal_query_bind]
  cases coordinate <;> simp [runResolvedFromTable]

theorem value_of_mem_runResolvedFromTable_revealCoordinateOutput
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (cache : SplitHashCache) (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table
        ((revealCoordinateOutput coordinate).run cache))) :
    result.context.state.values coordinate = some result.value.1 := by
  rw [runResolvedFromTable_revealCoordinateOutput] at hresult
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      cases hresolve : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp [hresolve] at hresult
      | some resolved =>
          simp [hresolve] at hresult
          subst result
          simp [LazyRevealProbe.State.materialize]
  | position position =>
      rw [mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          simp at hrest
          subst result
          simp [LazyRevealProbe.State.materialize]

theorem runResolvedFromTable_revealPosition
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (cache : SplitHashCache) :
    runResolvedFromTable context fuel table
        ((revealPosition position).run cache) = (do
      let resolved ← resolveDeferredReveal table position context
      match resolved with
      | none => pure none
      | some resolved =>
          pure (some ⟨
            { state := context.state.materialize (.position position) resolved.output
              values := resolved.values },
            fuel,
            (truncateHash resolved.output,
              Function.update cache (.hidden (.position position)) (some resolved.output)),
            table⟩)) := by
  rw [revealPosition, runResolvedFromTable_revealCoordinate]

theorem runResolvedFromTable_revealChainStart_of_agrees
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (cache : SplitHashCache) (hagrees : StartTableAgrees context.state table)
    (hclean : ¬context.state.hitAt index.coordinate (table index)) :
    runResolvedFromTable context fuel table
        ((revealChainStart index.lay index.tree index.leafIdx index.chainIdx).run cache) =
      pure (some ⟨
        { state := context.state.materialize index.coordinate (table index)
          values := context.values },
        fuel,
        (truncateHash (table index),
          Function.update cache (.hidden index.coordinate) (some (table index))),
        table⟩) := by
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  rw [revealChainStart, runResolvedFromTable_revealCoordinate]
  simp only [OtsSecretIndex.coordinate] at hagrees hclean ⊢
  rw [resolveDeferredChainStart_of_agrees table ⟨lay, tree, leafIdx, chainIdx⟩
    context hagrees hclean]
  simp [OtsSecretIndex.coordinate]

def ResolvedAdministrative
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (value : alpha) : Prop :=
  ∀ context cache fuel table, ∃ finalContext,
    runResolvedFromTable context fuel table (computation.run cache) =
      pure (some ⟨finalContext, fuel, (value, cache), table⟩) ∧
    finalContext.state.pending = context.state.pending ∧
    finalContext.state.values = context.state.values ∧
    finalContext.values = context.values

def ResolvedPreservesPublished
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha) : Prop :=
  ∀ context cache fuel table result,
    PublishedValues context.state →
    some result ∈ support
      (runResolvedFromTable context fuel table (computation.run cache)) →
    PublishedValues result.context.state

theorem PublishedValues.materialize
    {state : LazyRevealProbe.State Coordinate} (hpublished : PublishedValues state)
    (coordinate : Coordinate) (output : HashOutput) :
    PublishedValues (state.materialize coordinate output) := by
  intro other hrevealed
  by_cases heq : other = coordinate
  · subst other
    simp [LazyRevealProbe.State.materialize]
  · simpa [LazyRevealProbe.State.materialize, heq] using
      hpublished other hrevealed

theorem ResolvedPreservesPublished.pure (value : alpha) :
    ResolvedPreservesPublished
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha) := by
  intro context cache fuel table result hpublished hresult
  simp [runResolvedFromTable] at hresult
  subst result
  exact hpublished

theorem ResolvedPreservesPublished.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    (hleft : ResolvedPreservesPublished left)
    (hnext : ∀ value, ResolvedPreservesPublished (next value)) :
    ResolvedPreservesPublished (left >>= next) := by
  intro context cache fuel table result hpublished hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hrest⟩ := hresult
  cases middle with
  | none => simp at hrest
  | some middle =>
      exact hnext middle.value.1 middle.context middle.value.2 middle.remaining middle.table result
        (hleft context cache fuel table middle hpublished hmiddle) hrest

theorem resolvedPreservesPublished_ensureCoordinate (coordinate : Coordinate) :
    ResolvedPreservesPublished (ensureCoordinate coordinate) := by
  intro context cache fuel table result hpublished hresult
  unfold ensureCoordinate at hresult
  rw [StateT.run_liftM, LazyRevealProbe.ensureQuery,
    runResolvedFromTable_ensure_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  simpa [PublishedValues, LazyRevealProbe.State.ensure] using hpublished

theorem resolvedPreservesPublished_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (hcomponent : ∀ index, ResolvedPreservesPublished (computation index)) :
    ResolvedPreservesPublished (sequenceFin computation) := by
  induction n with
  | zero => simpa [sequenceFin] using ResolvedPreservesPublished.pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun _ =>
            ResolvedPreservesPublished.pure _

theorem resolvedAdministrative_pure (value : alpha) :
    ResolvedAdministrative
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
      value := by
  intro context cache fuel table
  exact ⟨context, by simp [runResolvedFromTable]⟩

theorem ResolvedAdministrative.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    {leftValue : alpha} {value : beta}
    (hleft : ResolvedAdministrative left leftValue)
    (hnext : ResolvedAdministrative (next leftValue) value) :
    ResolvedAdministrative (left >>= next) value := by
  intro context cache fuel table
  obtain ⟨middleContext, hleftRun, hleftPending, hleftValues, hleftDeferred⟩ :=
    hleft context cache fuel table
  obtain ⟨finalContext, hnextRun, hnextPending, hnextValues, hnextDeferred⟩ :=
    hnext middleContext cache fuel table
  refine ⟨finalContext, ?_, hnextPending.trans hleftPending,
    hnextValues.trans hleftValues, hnextDeferred.trans hleftDeferred⟩
  rw [StateT.run_bind, runResolvedFromTable_bind, hleftRun]
  simpa using hnextRun

theorem ResolvedAdministrative.run
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {value : alpha} (hadministrative : ResolvedAdministrative computation value)
    (context : DeferredContext) (cache : SplitHashCache) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    ∃ finalContext,
      runResolvedFromTable context fuel table (computation.run cache) =
        pure (some ⟨finalContext, fuel, (value, cache), table⟩) ∧
      finalContext.state.pending = context.state.pending ∧
      finalContext.state.values = context.state.values ∧
      finalContext.values = context.values :=
  hadministrative context cache fuel table

theorem resolvedAdministrative_ensureCoordinate (coordinate : Coordinate) :
    ResolvedAdministrative (ensureCoordinate coordinate) () := by
  intro context cache fuel table
  refine ⟨{ context with state := context.state.ensure coordinate }, ?_, rfl, rfl, rfl⟩
  unfold ensureCoordinate
  rw [StateT.run_liftM, LazyRevealProbe.ensureQuery,
    runResolvedFromTable_ensure_query_bind]
  simp [runResolvedFromTable]

theorem resolvedAdministrative_publishCoordinate (coordinate : Coordinate) :
    ResolvedAdministrative (publishCoordinate coordinate) () := by
  intro context cache fuel table
  refine ⟨{ context with state := context.state.publish coordinate }, ?_, rfl, rfl, rfl⟩
  unfold publishCoordinate
  rw [StateT.run_liftM, LazyRevealProbe.publishQuery,
    runResolvedFromTable_publish_query_bind]
  simp [runResolvedFromTable]

theorem resolvedAdministrative_sequenceFin {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (value : Fin n → alpha)
    (hcomponent : ∀ index, ResolvedAdministrative (computation index) (value index)) :
    ResolvedAdministrative (sequenceFin computation) value := by
  induction n with
  | zero =>
      have hvalue : value = Fin.elim0 := Subsingleton.elim _ _
      subst value
      simpa [sequenceFin] using
        (resolvedAdministrative_pure (value := Fin.elim0) :
          ResolvedAdministrative (pure Fin.elim0) Fin.elim0)
  | succ n ih =>
      rw [sequenceFin]
      have htail := ih (fun index : Fin n => computation index.succ)
        (fun index : Fin n => value index.succ) (fun index => hcomponent index.succ)
      let assembled : Fin (n + 1) → alpha :=
        Fin.cases (value 0) (fun index : Fin n => value index.succ)
      have hpure : ResolvedAdministrative
          (pure assembled : StateT SplitHashCache
            (OracleComp (LazyRevealProbe.World Coordinate)) (Fin (n + 1) → alpha))
          assembled := resolvedAdministrative_pure assembled
      have hrest : ResolvedAdministrative
          (sequenceFin (fun index : Fin n => computation index.succ) >>= fun tail =>
            pure (Fin.cases (value 0) tail)) assembled := by
        exact htail.bind hpure
      have hhead : ResolvedAdministrative
          (computation 0 >>= fun head =>
            sequenceFin (fun index : Fin n => computation index.succ) >>= fun tail =>
              pure (Fin.cases head tail)) assembled := by
        exact (hcomponent 0).bind hrest
      have hassembled : assembled = value := by
        funext index
        cases index using Fin.cases <;> rfl
      simpa only [hassembled] using hhead

theorem resolvedAdministrative_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ResolvedAdministrative (ensureFullChain lay tree leafIdx chainIdx) () := by
  unfold ensureFullChain
  apply ResolvedAdministrative.bind
    (resolvedAdministrative_sequenceFin
      (fun step : ChainStep =>
        ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step)))
      (fun _ => ())
      (fun step => resolvedAdministrative_ensureCoordinate
        (.position (.chain lay tree leafIdx chainIdx step))))
  exact resolvedAdministrative_pure ()

theorem resolvedPreservesPublished_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ResolvedPreservesPublished (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (resolvedPreservesPublished_sequenceFin
    (fun step : ChainStep =>
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step)))
    (fun step => resolvedPreservesPublished_ensureCoordinate
      (.position (.chain lay tree leafIdx chainIdx step)))).bind fun _ =>
        ResolvedPreservesPublished.pure ()

theorem resolvedAdministrative_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    ResolvedAdministrative (ensureChainPrefix lay tree leafIdx chainIdx digit) () := by
  unfold ensureChainPrefix
  apply ResolvedAdministrative.bind
    (resolvedAdministrative_sequenceFin
      (fun step : ChainStep =>
        if step.val < digit.val then
          ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))
        else pure ())
      (fun _ => ()) (fun step => by
        by_cases hstep : step.val < digit.val
        · rw [if_pos hstep]
          exact resolvedAdministrative_ensureCoordinate
            (.position (.chain lay tree leafIdx chainIdx step))
        · rw [if_neg hstep]
          exact resolvedAdministrative_pure ()))
  exact resolvedAdministrative_pure ()

theorem resolvedPreservesPublished_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    ResolvedPreservesPublished (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (resolvedPreservesPublished_sequenceFin
    (fun step : ChainStep =>
      if step.val < digit.val then
        ensureCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      else pure ())
    (fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact resolvedPreservesPublished_ensureCoordinate _
      · rw [if_neg hstep]
        exact ResolvedPreservesPublished.pure ())).bind fun _ =>
          ResolvedPreservesPublished.pure ()

theorem resolvedAdministrative_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedAdministrative (ensureOtsLeaf lay tree leafIdx) () := by
  unfold ensureOtsLeaf
  have hchains := resolvedAdministrative_sequenceFin
    (fun chainIdx : ChainIndex => ensureFullChain lay tree leafIdx chainIdx)
    (fun _ => ()) (fun chainIdx =>
      resolvedAdministrative_ensureFullChain lay tree leafIdx chainIdx)
  exact hchains.bind
    (resolvedAdministrative_ensureCoordinate (.position (.leaf lay tree leafIdx)))

theorem resolvedPreservesPublished_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesPublished (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (resolvedPreservesPublished_sequenceFin
    (fun chainIdx : ChainIndex => ensureFullChain lay tree leafIdx chainIdx)
    (fun chainIdx => resolvedPreservesPublished_ensureFullChain lay tree leafIdx chainIdx)).bind
      fun _ => resolvedPreservesPublished_ensureCoordinate (.position (.leaf lay tree leafIdx))

theorem resolvedAdministrative_ensureTreeNode (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, ResolvedAdministrative (ensureTreeNode lay tree level nodeIdx) ()
  | 0, nodeIdx => resolvedAdministrative_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      apply ResolvedAdministrative.bind
        (resolvedAdministrative_ensureTreeNode lay tree level (2 * nodeIdx))
      apply ResolvedAdministrative.bind
        (resolvedAdministrative_ensureTreeNode lay tree level (2 * nodeIdx + 1))
      by_cases hlevel : level < maxLayerHeight
      · rw [dif_pos hlevel]
        exact resolvedAdministrative_ensureCoordinate
          (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
      · rw [dif_neg hlevel]
        exact resolvedAdministrative_pure ()

theorem resolvedPreservesPublished_ensureTreeNode (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx, ResolvedPreservesPublished (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => resolvedPreservesPublished_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (resolvedPreservesPublished_ensureTreeNode lay tree level (2 * nodeIdx)).bind
        fun _ => (resolvedPreservesPublished_ensureTreeNode lay tree level
          (2 * nodeIdx + 1)).bind fun _ => by
            by_cases hlevel : level < maxLayerHeight
            · rw [dif_pos hlevel]
              exact resolvedPreservesPublished_ensureCoordinate _
            · rw [dif_neg hlevel]
              exact ResolvedPreservesPublished.pure ()

theorem resolvedAdministrative_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedAdministrative (ensureTreePath lay tree leafIdx) () := by
  unfold ensureTreePath
  apply ResolvedAdministrative.bind
    (resolvedAdministrative_sequenceFin
      (fun level : Fin maxLayerHeight =>
        if level.val < layerHeight lay then
          ensureTreeNode lay tree level.val
            (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
        else pure ())
      (fun _ => ()) (fun level => by
        by_cases hlevel : level.val < layerHeight lay
        · rw [if_pos hlevel]
          exact resolvedAdministrative_ensureTreeNode lay tree level.val
            (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
        · rw [if_neg hlevel]
          exact resolvedAdministrative_pure ()))
  exact resolvedAdministrative_pure ()

theorem resolvedPreservesPublished_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesPublished (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (resolvedPreservesPublished_sequenceFin
    (fun level : Fin maxLayerHeight =>
      if level.val < layerHeight lay then
        ensureTreeNode lay tree level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      else pure ())
    (fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact resolvedPreservesPublished_ensureTreeNode lay tree level.val _
      · rw [if_neg hlevel]
        exact ResolvedPreservesPublished.pure ())).bind fun _ =>
          ResolvedPreservesPublished.pure ()

theorem runResolvedFromTable_maskedChainValue_zero
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (hdigit : digit.val = 0)
    (context : DeferredContext) (cache : SplitHashCache) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hagrees : StartTableAgrees context.state table)
    (hclean : ¬context.state.hitAt
      (.chainStart lay tree leafIdx chainIdx) (table ⟨lay, tree, leafIdx, chainIdx⟩)) :
    ∃ reservedContext : DeferredContext,
      runResolvedFromTable context fuel table
          ((maskedChainValue lay tree leafIdx chainIdx digit).run cache) =
        pure (some ⟨
          { state := reservedContext.state.materialize
              (.chainStart lay tree leafIdx chainIdx)
              (table ⟨lay, tree, leafIdx, chainIdx⟩)
            values := reservedContext.values },
          fuel,
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            Function.update cache (.hidden (.chainStart lay tree leafIdx chainIdx))
              (some (table ⟨lay, tree, leafIdx, chainIdx⟩))),
          table⟩) := by
  obtain ⟨reservedContext, hreserve, hpending, hstateValues, _hdeferred⟩ :=
    (resolvedAdministrative_ensureChainPrefix lay tree leafIdx chainIdx digit).run
      context cache fuel table
  have hreservedAgrees : StartTableAgrees reservedContext.state table := by
    intro index output hvalue
    apply hagrees index output
    rw [← hstateValues]
    exact hvalue
  have hreservedClean : ¬reservedContext.state.hitAt
      (.chainStart lay tree leafIdx chainIdx) (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
    unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt at hclean ⊢
    rw [hpending]
    exact hclean
  refine ⟨reservedContext, ?_⟩
  unfold maskedChainValue
  rw [StateT.run_bind, runResolvedFromTable_bind, hreserve]
  simp only [pure_bind]
  rw [dif_pos hdigit]
  exact runResolvedFromTable_revealChainStart_of_agrees reservedContext fuel table
    ⟨lay, tree, leafIdx, chainIdx⟩ cache hreservedAgrees hreservedClean

theorem runResolvedFromTable_maskedChainValue_positive
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (hdigit : digit.val ≠ 0)
    (context : DeferredContext) (cache : SplitHashCache) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    let step : ChainStep := ⟨digit.val - 1, by
      have := digit.isLt
      omega⟩
    ∃ reservedContext : DeferredContext,
      runResolvedFromTable context fuel table
          ((maskedChainValue lay tree leafIdx chainIdx digit).run cache) = (do
        let resolved ← resolveDeferredPosition table
          (.chain lay tree leafIdx chainIdx step) reservedContext
        match resolved with
        | none => pure none
        | some resolved =>
            pure (some ⟨
              { state := reservedContext.state.materialize
                  (.position (.chain lay tree leafIdx chainIdx step)) resolved.output
                values := resolved.values },
              fuel,
              (truncateHash resolved.output,
                Function.update cache
                  (.hidden (.position (.chain lay tree leafIdx chainIdx step)))
                  (some resolved.output)),
              table⟩)) := by
  dsimp only
  obtain ⟨reservedContext, hreserve, _hpending, _hstateValues, _hdeferred⟩ :=
    (resolvedAdministrative_ensureChainPrefix lay tree leafIdx chainIdx digit).run
      context cache fuel table
  refine ⟨reservedContext, ?_⟩
  unfold maskedChainValue
  rw [StateT.run_bind, runResolvedFromTable_bind, hreserve]
  simp only [pure_bind]
  rw [dif_neg hdigit]
  simpa [resolveDeferredReveal, ResolvableOtsPosition] using
    runResolvedFromTable_revealPosition reservedContext fuel table
      (.chain lay tree leafIdx chainIdx ⟨digit.val - 1, by
        have := digit.isLt
        omega⟩) cache

noncomputable def finalizeResolvedCoordinates
    (coordinates : List Coordinate) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput) :
    ProbComp (Option DeferredContext) :=
  match coordinates with
  | [] => pure (some context)
  | coordinate :: remaining =>
      match context.state.values coordinate with
      | some _ =>
          finalizeResolvedCoordinates remaining
            { context with state := context.state.clearPending coordinate } table
      | none => do
          let resolved ← match coordinate with
            | .chainStart lay tree leafIdx chainIdx =>
                pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context)
            | .position position => resolveDeferredPositionValue position context
          match resolved with
          | none => pure none
          | some resolved =>
              finalizeResolvedCoordinates remaining
                { state := resolved.state.complete coordinate resolved.output
                  values := resolved.values }
                table

@[simp] theorem clearPending_complete_self
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) :
    (state.clearPending coordinate).complete coordinate output =
      state.complete coordinate output := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.complete,
    LazyRevealProbe.State.pendingAway]

theorem finalizeResolvedCoordinates_cons_of_state_value
    (coordinate : Coordinate) (remaining : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (output : HashOutput) (hvalue : context.state.values coordinate = some output) :
    finalizeResolvedCoordinates (coordinate :: remaining) context table =
      finalizeResolvedCoordinates remaining
        { context with state := context.state.clearPending coordinate } table := by
  rw [finalizeResolvedCoordinates]
  simp [hvalue]

theorem finalizeResolvedCoordinates_cons_position_of_deferred_value
    (position : Position) (remaining : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (output : HashOutput)
    (hstate : context.state.values (.position position) = none)
    (hvalue : context.values position = some output) :
    finalizeResolvedCoordinates (.position position :: remaining) context table =
      if context.state.hitAt (.position position) output then
        (pure none : ProbComp (Option DeferredContext))
      else finalizeResolvedCoordinates remaining
        { state := context.state.complete (.position position) output
          values := context.values }
        table := by
  rw [finalizeResolvedCoordinates]
  simp only [hstate]
  rw [resolveDeferredPositionValue_of_deferred_value position context output hstate hvalue]
  by_cases hhit : context.state.hitAt (.position position) output
  · simp [hhit]
  · simp only [hhit, ↓reduceIte, pure_bind]
    rw [clearPending_complete_self]

theorem finalizeResolvedCoordinates_cons_position_fresh
    (position : Position) (remaining : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position position) = none)
    (hvalue : context.values position = none) :
    finalizeResolvedCoordinates (.position position :: remaining) context table = (do
      let output ← LazyRevealProbe.sampleHashOutput
      (if context.state.hitAt (.position position) output then
        (pure none : ProbComp (Option DeferredContext))
      else finalizeResolvedCoordinates remaining
        ({ state := context.state.complete (.position position) output
           values := context.values.install position output } : DeferredContext)
        table)) := by
  rw [finalizeResolvedCoordinates]
  simp only [hstate]
  rw [resolveDeferredPositionValue_fresh position context hstate hvalue]
  simp only [bind_assoc]
  apply bind_congr
  intro output
  by_cases hhit : context.state.hitAt (.position position) output
  · simp [hhit]
  · simp only [hhit, ↓reduceIte, pure_bind]
    rw [clearPending_complete_self]

theorem resolveDeferredChainStart_of_missing
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext)
    (hmissing : context.state.values index.coordinate = none) :
    resolveDeferredChainStart table index context =
      if context.state.hitAt index.coordinate (table index) then none
      else some ⟨
        { state := context.state.clearPending index.coordinate
          values := context.values },
        table index⟩ := by
  simp [resolveDeferredChainStart, hmissing]

noncomputable def resolvedCompletionOutput (coordinate : Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) : ProbComp HashOutput :=
  match coordinate with
  | .chainStart lay tree leafIdx chainIdx => pure (table ⟨lay, tree, leafIdx, chainIdx⟩)
  | .position position =>
      match context.values position with
      | some output => pure output
      | none => LazyRevealProbe.sampleHashOutput

def DeferredContext.completeResolved (context : DeferredContext)
    (coordinate : Coordinate) (output : HashOutput) : DeferredContext :=
  match coordinate with
  | .chainStart _ _ _ _ =>
      { context with state := context.state.complete coordinate output }
  | .position position =>
      { state := context.state.complete coordinate output
        values := context.values.install position output }

theorem resolvedCompletionOutput_neverFails
    (coordinate : Coordinate) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput) :
    Pr[⊥ | resolvedCompletionOutput coordinate context table] = 0 := by
  cases coordinate with
  | chainStart => simp [resolvedCompletionOutput]
  | position position =>
      cases context.values position <;>
        simp [resolvedCompletionOutput, LazyRevealProbe.sampleHashOutput]

theorem finalizeResolvedCoordinates_cons_of_missing
    (coordinate : Coordinate) (remaining : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hmissing : context.state.values coordinate = none) :
    finalizeResolvedCoordinates (coordinate :: remaining) context table = (do
      let output ← resolvedCompletionOutput coordinate context table
      (if context.state.hitAt coordinate output then
        (pure none : ProbComp (Option DeferredContext))
      else finalizeResolvedCoordinates remaining
        (context.completeResolved coordinate output) table)) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
      have hmissing' : context.state.values index.coordinate = none := by
        simpa [index, OtsSecretIndex.coordinate] using hmissing
      rw [finalizeResolvedCoordinates]
      simp only [hmissing]
      rw [resolveDeferredChainStart_of_missing table index context hmissing']
      by_cases hhit : context.state.hitAt (.chainStart lay tree leafIdx chainIdx)
          (table ⟨lay, tree, leafIdx, chainIdx⟩)
      · simp [resolvedCompletionOutput, DeferredContext.completeResolved, index,
          OtsSecretIndex.coordinate, hhit]
      · simp [resolvedCompletionOutput, DeferredContext.completeResolved, index,
          OtsSecretIndex.coordinate, hhit]
  | position position =>
      cases hvalue : context.values position with
      | some output =>
          rw [finalizeResolvedCoordinates_cons_position_of_deferred_value position remaining
            context table output hmissing hvalue]
          have hinstall : context.values.install position output = context.values := by
            funext other
            by_cases heq : other = position
            · subst other
              simp [DeferredStructuralValues.install, hvalue]
            · simp [DeferredStructuralValues.install, heq]
          simp [resolvedCompletionOutput, DeferredContext.completeResolved, hvalue, hinstall]
      | none =>
          rw [finalizeResolvedCoordinates_cons_position_fresh position remaining context table
            hmissing hvalue]
          simp [resolvedCompletionOutput, DeferredContext.completeResolved, hvalue]

theorem resolvedCompletionOutput_completeResolved_of_ne
    (left right : Coordinate) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput) (output : HashOutput) (hne : right ≠ left) :
    resolvedCompletionOutput right (context.completeResolved left output) table =
      resolvedCompletionOutput right context table := by
  cases left with
  | chainStart => cases right <;> rfl
  | position left =>
      cases right with
      | chainStart => rfl
      | position right =>
          have hposition : right ≠ left := by
            intro heq
            subst right
            exact hne rfl
          simp [resolvedCompletionOutput, DeferredContext.completeResolved,
            DeferredStructuralValues.install, hposition]

theorem DeferredContext.completeResolved_comm
    (context : DeferredContext) (left right : Coordinate)
    (leftOutput rightOutput : HashOutput) (hne : left ≠ right) :
    (context.completeResolved left leftOutput).completeResolved right rightOutput =
      (context.completeResolved right rightOutput).completeResolved left leftOutput := by
  have hstate := complete_comm context.state left right leftOutput rightOutput hne
  cases left with
  | chainStart =>
      cases right with
      | chainStart =>
          simp [DeferredContext.completeResolved, hstate]
      | position right =>
          simp [DeferredContext.completeResolved, hstate]
  | position left =>
      cases right with
      | chainStart =>
          simp [DeferredContext.completeResolved, hstate]
      | position right =>
          have hposition : left ≠ right := by
            intro heq
            subst right
            exact hne rfl
          rcases context with ⟨state, values⟩
          simp only [DeferredContext.completeResolved]
          rw [complete_comm state (.position left) (.position right)
            leftOutput rightOutput hne]
          congr 1
          exact Function.update_comm hposition (some leftOutput) (some rightOutput) values

set_option maxRecDepth 100000 in
theorem evalDist_finalizeResolvedCoordinates_two_missing
    (left right : Coordinate) (remaining : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hne : left ≠ right) (hleft : context.state.values left = none)
    (hright : context.state.values right = none) :
    evalDist (finalizeResolvedCoordinates (left :: right :: remaining) context table) =
      evalDist (do
        let leftOutput ← resolvedCompletionOutput left context table
        let rightOutput ← resolvedCompletionOutput right context table
        (if context.state.hitAt left leftOutput then
          (pure none : ProbComp (Option DeferredContext))
        else if context.state.hitAt right rightOutput then
          pure none
        else finalizeResolvedCoordinates remaining
          (((context.completeResolved left leftOutput).completeResolved right rightOutput) :
            DeferredContext) table)) := by
  rw [finalizeResolvedCoordinates_cons_of_missing left (right :: remaining) context table hleft]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro leftOutput
  by_cases hleftHit : context.state.hitAt left leftOutput
  · rw [if_pos hleftHit]
    simp only [hleftHit, ↓reduceIte]
    exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (resolvedCompletionOutput right context table)
      (resolvedCompletionOutput_neverFails right context table) (pure none) |>.symm
  · rw [if_neg hleftHit]
    simp only [hleftHit, ↓reduceIte]
    have hrightValue : (context.completeResolved left leftOutput).state.values right = none := by
      cases left <;> simp only [DeferredContext.completeResolved] <;>
        rw [values_complete_of_ne context.state _ right leftOutput (Ne.symm hne), hright]
    rw [finalizeResolvedCoordinates_cons_of_missing right remaining
      (context.completeResolved left leftOutput) table hrightValue]
    rw [resolvedCompletionOutput_completeResolved_of_ne left right context table leftOutput
      (Ne.symm hne)]
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro rightOutput
    have hcompleteState :
        (context.completeResolved left leftOutput).state =
          context.state.complete left leftOutput := by
      cases left <;> rfl
    have hrightHit :
        (context.completeResolved left leftOutput).state.hitAt right rightOutput ↔
          context.state.hitAt right rightOutput := by
      rw [hcompleteState]
      exact hitAt_complete_of_ne context.state left right leftOutput rightOutput (Ne.symm hne)
    by_cases hhit : context.state.hitAt right rightOutput
    · rw [if_pos (hrightHit.mpr hhit), if_pos hhit]
    · rw [if_neg (mt hrightHit.mp hhit), if_neg hhit]

set_option maxRecDepth 100000 in
theorem evalDist_finalizeResolvedCoordinates_swap_of_both_missing
    (left right : Coordinate) (remaining : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hne : left ≠ right) (hleft : context.state.values left = none)
    (hright : context.state.values right = none) :
    evalDist (finalizeResolvedCoordinates (left :: right :: remaining) context table) =
      evalDist (finalizeResolvedCoordinates (right :: left :: remaining) context table) := by
  rw [evalDist_finalizeResolvedCoordinates_two_missing left right remaining context table hne
    hleft hright,
    evalDist_finalizeResolvedCoordinates_two_missing right left remaining context table hne.symm
      hright hleft]
  rw [OracleComp.DeferredSampling.evalDist_bind_comm
    (resolvedCompletionOutput left context table)
    (resolvedCompletionOutput right context table)]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro rightOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro leftOutput
  by_cases hleftHit : context.state.hitAt left leftOutput
  · simp [hleftHit]
  · by_cases hrightHit : context.state.hitAt right rightOutput
    · simp [hleftHit, hrightHit]
    · simp only [hleftHit, hrightHit, ↓reduceIte]
      rw [DeferredContext.completeResolved_comm context left right leftOutput rightOutput hne]

theorem clearPending_completeResolved_comm
    (context : DeferredContext) (left right : Coordinate) (output : HashOutput) :
    ({ context with state := context.state.clearPending left }).completeResolved right output =
      { context.completeResolved right output with
        state := (context.completeResolved right output).state.clearPending left } := by
  cases right <;> simp only [DeferredContext.completeResolved] <;>
    rw [clearPending_complete_comm]

set_option maxRecDepth 100000 in
theorem evalDist_finalizeResolvedCoordinates_swap_of_some_none
    (left right : Coordinate) (remaining : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (leftOutput : HashOutput) (hne : left ≠ right)
    (hleft : context.state.values left = some leftOutput)
    (hright : context.state.values right = none) :
    evalDist (finalizeResolvedCoordinates (left :: right :: remaining) context table) =
      evalDist (finalizeResolvedCoordinates (right :: left :: remaining) context table) := by
  rw [finalizeResolvedCoordinates_cons_of_state_value left (right :: remaining) context table
    leftOutput hleft]
  have hrightClear :
      (context.state.clearPending left).values right = none := by
    simpa only [values_clearPending] using hright
  rw [finalizeResolvedCoordinates_cons_of_missing right remaining
    { context with state := context.state.clearPending left } table hrightClear]
  rw [finalizeResolvedCoordinates_cons_of_missing right (left :: remaining) context table hright]
  have hcompletionOutput : resolvedCompletionOutput right
      { context with state := context.state.clearPending left } table =
        resolvedCompletionOutput right context table := by
    cases right <;> rfl
  rw [hcompletionOutput]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro rightOutput
  have hrightHit : (context.state.clearPending left).hitAt right rightOutput ↔
      context.state.hitAt right rightOutput :=
    hitAt_clearPending_of_ne context.state left right rightOutput hne.symm
  by_cases hhit : context.state.hitAt right rightOutput
  · rw [if_pos (hrightHit.mpr hhit), if_pos hhit]
  · rw [if_neg (mt hrightHit.mp hhit), if_neg hhit]
    have hleftCompleted :
        (context.completeResolved right rightOutput).state.values left = some leftOutput := by
      have hstate : (context.completeResolved right rightOutput).state =
          context.state.complete right rightOutput := by
        cases right <;> rfl
      rw [hstate, values_complete_of_ne context.state right left rightOutput hne, hleft]
    rw [finalizeResolvedCoordinates_cons_of_state_value left remaining
      (context.completeResolved right rightOutput) table leftOutput hleftCompleted]
    rw [clearPending_completeResolved_comm context left right rightOutput]

set_option maxRecDepth 100000 in
theorem evalDist_finalizeResolvedCoordinates_swap
    (left right : Coordinate) (remaining : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hne : left ≠ right) :
    evalDist (finalizeResolvedCoordinates (left :: right :: remaining) context table) =
      evalDist (finalizeResolvedCoordinates (right :: left :: remaining) context table) := by
  cases hleft : context.state.values left with
  | some leftOutput =>
      cases hright : context.state.values right with
      | some rightOutput =>
          rw [finalizeResolvedCoordinates_cons_of_state_value left (right :: remaining)
            context table leftOutput hleft,
            finalizeResolvedCoordinates_cons_of_state_value right (left :: remaining)
              context table rightOutput hright]
          have hrightClear : (context.state.clearPending left).values right =
              some rightOutput := by simpa only [values_clearPending] using hright
          have hleftClear : (context.state.clearPending right).values left =
              some leftOutput := by simpa only [values_clearPending] using hleft
          rw [finalizeResolvedCoordinates_cons_of_state_value right remaining
            { context with state := context.state.clearPending left } table rightOutput hrightClear,
            finalizeResolvedCoordinates_cons_of_state_value left remaining
              { context with state := context.state.clearPending right } table leftOutput hleftClear]
          rw [clearPending_comm]
      | none =>
          exact evalDist_finalizeResolvedCoordinates_swap_of_some_none left right remaining
            context table leftOutput hne hleft hright
  | none =>
      cases hright : context.state.values right with
      | some rightOutput =>
          exact (evalDist_finalizeResolvedCoordinates_swap_of_some_none right left remaining
            context table rightOutput hne.symm hright hleft).symm
      | none =>
          exact evalDist_finalizeResolvedCoordinates_swap_of_both_missing left right remaining
            context table hne hleft hright

set_option maxRecDepth 100000 in
theorem evalDist_finalizeResolvedCoordinates_perm
    {left right : List Coordinate} (hperm : left.Perm right)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) :
    evalDist (finalizeResolvedCoordinates left context table) =
      evalDist (finalizeResolvedCoordinates right context table) := by
  induction hperm generalizing context with
  | nil => rfl
  | cons coordinate hperm ih =>
      cases hvalue : context.state.values coordinate with
      | some output =>
          rw [finalizeResolvedCoordinates_cons_of_state_value coordinate _ context table output
            hvalue,
            finalizeResolvedCoordinates_cons_of_state_value coordinate _ context table output
              hvalue]
          exact ih { context with state := context.state.clearPending coordinate }
      | none =>
          rw [finalizeResolvedCoordinates_cons_of_missing coordinate _ context table hvalue,
            finalizeResolvedCoordinates_cons_of_missing coordinate _ context table hvalue]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          by_cases hhit : context.state.hitAt coordinate output
          · rw [if_pos hhit, if_pos hhit]
          · rw [if_neg hhit, if_neg hhit]
            exact ih (context.completeResolved coordinate output)
  | swap left right remaining =>
      by_cases heq : left = right
      · subst right
        rfl
      · exact (evalDist_finalizeResolvedCoordinates_swap left right remaining context table
          heq).symm
  | trans _ _ ihLeft ihRight => exact (ihLeft context).trans (ihRight context)

theorem evalDist_finalizeResolvedCoordinates_move_to_front
    (coordinate : Coordinate) (coordinates : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hmem : coordinate ∈ coordinates) :
    evalDist (finalizeResolvedCoordinates coordinates context table) =
      evalDist (finalizeResolvedCoordinates
        (coordinate :: coordinates.erase coordinate) context table) :=
  evalDist_finalizeResolvedCoordinates_perm (List.perm_cons_erase hmem) context table

def DeferredContext.presamplePosition (context : DeferredContext)
    (position : Position) (output : HashOutput) : DeferredContext :=
  { state := context.state.clearPending (.position position)
    values := context.values.install position output }

theorem not_hitAt_clearPending_self
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) :
    ¬(state.clearPending coordinate).hitAt coordinate output := by
  simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt,
    LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway]

theorem clearPending_eq_self_of_not_mem_coordinates
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (hnotMem : coordinate ∉ state.coordinates) :
    state.clearPending coordinate = state := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp only [LazyRevealProbe.State.clearPending]
  congr 1
  apply Finset.filter_eq_self.2
  intro entry hentry
  simp only [ne_eq]
  intro heq
  apply hnotMem
  apply Finset.mem_union_right
  apply Finset.mem_image.2
  exact ⟨entry, hentry, heq⟩

theorem not_hitAt_of_not_mem_coordinates
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) (hnotMem : coordinate ∉ state.coordinates) :
    ¬state.hitAt coordinate output := by
  have hclear := clearPending_eq_self_of_not_mem_coordinates state coordinate hnotMem
  simpa only [hclear] using not_hitAt_clearPending_self state coordinate output

theorem DeferredContext.Valid.clearPending
    {context : DeferredContext} (hvalid : context.Valid)
    (coordinate : Coordinate) :
    ({ context with state := context.state.clearPending coordinate } :
      DeferredContext).Valid := by
  constructor
  · intro position output hvalue
    exact hvalid.1 position output hvalue
  · intro other output hvalue
    by_cases heq : other = coordinate
    · subst other
      exact not_hitAt_clearPending_self context.state coordinate output
    · exact (hitAt_clearPending_of_ne context.state coordinate other output heq).not.mpr
        (hvalid.2 other output hvalue)

theorem DeferredContext.Valid.clearPending_install
    {context : DeferredContext} (hvalid : context.Valid)
    (position : Position) (output : HashOutput)
    (hcompatible : ∀ existing,
      context.state.values (.position position) = some existing → existing = output) :
    ({ state := context.state.clearPending (.position position)
       values := context.values.install position output } : DeferredContext).Valid := by
  constructor
  · intro other otherOutput hvalue
    by_cases heq : other = position
    · subst other
      have hsame : otherOutput = output := hcompatible otherOutput hvalue
      subst otherOutput
      simp [DeferredStructuralValues.install]
    · simpa [DeferredStructuralValues.install, heq] using
        hvalid.1 other otherOutput hvalue
  · intro coordinate candidate hvalue
    by_cases heq : coordinate = .position position
    · subst coordinate
      exact not_hitAt_clearPending_self context.state (.position position) candidate
    · exact (hitAt_clearPending_of_ne context.state (.position position)
        coordinate candidate heq).not.mpr (hvalid.2 coordinate candidate hvalue)

set_option maxRecDepth 100000 in
theorem evalDist_finalizeResolvedCoordinates_defer_position
    (position : Position) (coordinates : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hmem : Coordinate.position position ∈ coordinates)
    (hstate : context.state.values (.position position) = none)
    (hvalue : context.values position = none) :
    evalDist (finalizeResolvedCoordinates coordinates context table) =
      evalDist (do
        let output ← LazyRevealProbe.sampleHashOutput
        (if context.state.hitAt (.position position) output then
          (pure none : ProbComp (Option DeferredContext))
        else finalizeResolvedCoordinates coordinates
          (context.presamplePosition position output) table)) := by
  calc
    _ = evalDist (finalizeResolvedCoordinates
        (.position position :: coordinates.erase (.position position)) context table) :=
      evalDist_finalizeResolvedCoordinates_move_to_front (.position position) coordinates
        context table hmem
    _ = evalDist (do
        let output ← LazyRevealProbe.sampleHashOutput
        (if context.state.hitAt (.position position) output then
          (pure none : ProbComp (Option DeferredContext))
        else finalizeResolvedCoordinates (coordinates.erase (.position position))
          ({ state := context.state.complete (.position position) output
             values := context.values.install position output } : DeferredContext)
          table)) := congrArg evalDist
      (finalizeResolvedCoordinates_cons_position_fresh position
        (coordinates.erase (.position position)) context table hstate hvalue)
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit]
      · simp only [hhit, ↓reduceIte]
        have hpresampledState :
            (context.presamplePosition position output).state.values
              (.position position) = none := by
          exact hstate
        have hpresampledValue :
            (context.presamplePosition position output).values position = some output := by
          simp [DeferredContext.presamplePosition, DeferredStructuralValues.install]
        have hhead := finalizeResolvedCoordinates_cons_position_of_deferred_value position
          (coordinates.erase (.position position)) (context.presamplePosition position output)
            table output hpresampledState hpresampledValue
        have hclean : ¬(context.presamplePosition position output).state.hitAt
            (.position position) output :=
          not_hitAt_clearPending_self context.state (.position position) output
        have hmove := evalDist_finalizeResolvedCoordinates_move_to_front
          (.position position) coordinates (context.presamplePosition position output) table hmem
        rw [hhead, if_neg hclean] at hmove
        have hcompleted :
            ({ state := (context.presamplePosition position output).state.complete
                (.position position) output
               values := (context.presamplePosition position output).values } :
              DeferredContext) =
              ({ state := context.state.complete (.position position) output
                 values := context.values.install position output } : DeferredContext) := by
          simp [DeferredContext.presamplePosition]
        rw [hcompleted] at hmove
        exact hmove.symm

theorem evalDist_resolveDeferredPositionValue_fresh_then_finalize
    (position : Position) (coordinates : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hmem : Coordinate.position position ∈ coordinates)
    (hstate : context.state.values (.position position) = none)
    (hvalue : context.values position = none) :
    evalDist (do
        let resolved ← resolveDeferredPositionValue position context
        (match resolved with
        | none => (pure none : ProbComp (Option DeferredContext))
        | some resolved => finalizeResolvedCoordinates coordinates
            (resolved.toDeferredContext) table)) =
      evalDist (finalizeResolvedCoordinates coordinates context table) := by
  rw [resolveDeferredPositionValue_fresh position context hstate hvalue]
  simp only [bind_assoc]
  rw [evalDist_finalizeResolvedCoordinates_defer_position position coordinates context table
    hmem hstate hvalue]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro output
  by_cases hhit : context.state.hitAt (.position position) output
  · simp [hhit]
  · simp [hhit, DeferredContext.presamplePosition]

@[simp] theorem clearPending_idem
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) :
    (state.clearPending coordinate).clearPending coordinate =
      state.clearPending coordinate := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway]

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_finalize
    (position : Position) (coordinates : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hmem : Coordinate.position position ∈ coordinates)
    (hmaterialized : ∀ output,
      context.state.values (.position position) = some output →
        context.values position = some output ∧
          ¬context.state.hitAt (.position position) output) :
    evalDist (do
        let resolved ← resolveDeferredPositionValue position context
        (match resolved with
        | none => (pure none : ProbComp (Option DeferredContext))
        | some resolved => finalizeResolvedCoordinates coordinates
            resolved.toDeferredContext table)) =
      evalDist (finalizeResolvedCoordinates coordinates context table) := by
  cases hstate : context.state.values (.position position) with
  | some output =>
      obtain ⟨hvalue, hclean⟩ := hmaterialized output hstate
      rw [resolveDeferredPositionValue_of_state_value position context output hstate,
        if_neg hclean]
      simp only [pure_bind]
      have hinstall : context.values.install position output = context.values := by
        funext other
        by_cases heq : other = position
        · subst other
          simp [DeferredStructuralValues.install, hvalue]
        · simp [DeferredStructuralValues.install, heq]
      have hclearedValue :
          (context.state.clearPending (.position position)).values
              (.position position) = some output := by
        exact hstate
      calc
        evalDist (finalizeResolvedCoordinates coordinates
            { state := context.state.clearPending (.position position)
              values := context.values.install position output } table) =
            evalDist (finalizeResolvedCoordinates
              (.position position :: coordinates.erase (.position position))
              { state := context.state.clearPending (.position position)
                values := context.values.install position output } table) :=
          (evalDist_finalizeResolvedCoordinates_move_to_front
            (.position position) coordinates
            { state := context.state.clearPending (.position position)
              values := context.values.install position output }
            table hmem)
        _ = evalDist (finalizeResolvedCoordinates
              (coordinates.erase (.position position))
              { state := context.state.clearPending (.position position)
                values := context.values } table) := by
          rw [finalizeResolvedCoordinates_cons_of_state_value
            (.position position) (coordinates.erase (.position position))
            { state := context.state.clearPending (.position position)
              values := context.values.install position output }
            table output hclearedValue]
          simp [hinstall]
        _ = evalDist (finalizeResolvedCoordinates
              (.position position :: coordinates.erase (.position position))
              context table) := by
          rw [finalizeResolvedCoordinates_cons_of_state_value
            (.position position) (coordinates.erase (.position position))
            context table output hstate]
        _ = evalDist (finalizeResolvedCoordinates coordinates context table) :=
          evalDist_finalizeResolvedCoordinates_move_to_front
            (.position position) coordinates context table hmem |>.symm
  | none =>
      cases hvalue : context.values position with
      | none =>
          exact evalDist_resolveDeferredPositionValue_fresh_then_finalize position coordinates
            context table hmem hstate hvalue
      | some output =>
          rw [resolveDeferredPositionValue_of_deferred_value position context output hstate
            hvalue]
          by_cases hhit : context.state.hitAt (.position position) output
          · rw [if_pos hhit]
            simp only [pure_bind]
            have hmove := evalDist_finalizeResolvedCoordinates_move_to_front
              (.position position) coordinates context table hmem
            rw [finalizeResolvedCoordinates_cons_position_of_deferred_value position
              (coordinates.erase (.position position)) context table output hstate hvalue,
              if_pos hhit] at hmove
            simpa using hmove.symm
          · rw [if_neg hhit]
            simp only [pure_bind]
            have hclearedState :
                (context.state.clearPending (.position position)).values
                    (.position position) = none := hstate
            have hclearedValue : context.values position = some output := hvalue
            have hclearedClean :
                ¬(context.state.clearPending (.position position)).hitAt
                  (.position position) output :=
              not_hitAt_clearPending_self context.state (.position position) output
            calc
              evalDist (finalizeResolvedCoordinates coordinates
                  { state := context.state.clearPending (.position position)
                    values := context.values } table) =
                  evalDist (finalizeResolvedCoordinates
                    (.position position :: coordinates.erase (.position position))
                    { state := context.state.clearPending (.position position)
                      values := context.values } table) :=
                (evalDist_finalizeResolvedCoordinates_move_to_front
                  (.position position) coordinates
                  { state := context.state.clearPending (.position position)
                    values := context.values }
                  table hmem)
              _ = evalDist (finalizeResolvedCoordinates
                    (coordinates.erase (.position position))
                    { state := context.state.complete (.position position) output
                      values := context.values } table) := by
                rw [finalizeResolvedCoordinates_cons_position_of_deferred_value position
                  (coordinates.erase (.position position))
                  { state := context.state.clearPending (.position position)
                    values := context.values }
                  table output hclearedState hclearedValue,
                  if_neg hclearedClean, clearPending_complete_self]
              _ = evalDist (finalizeResolvedCoordinates
                    (.position position :: coordinates.erase (.position position))
                    context table) := by
                rw [finalizeResolvedCoordinates_cons_position_of_deferred_value position
                  (coordinates.erase (.position position)) context table output hstate hvalue,
                  if_neg hhit]
              _ = evalDist (finalizeResolvedCoordinates coordinates context table) :=
                evalDist_finalizeResolvedCoordinates_move_to_front
                  (.position position) coordinates context table hmem |>.symm

theorem DeferredContext.Valid.of_resolveDeferredPositionValue
    {context : DeferredContext} (hvalid : context.Valid)
    (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.toDeferredContext.Valid := by
  cases hstate : context.state.values (.position position) with
  | some output =>
      have hclean := hvalid.2 (.position position) output hstate
      rw [resolveDeferredPositionValue_of_state_value position context output hstate,
        if_neg hclean] at hresult
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hresult
      subst result
      apply hvalid.clearPending_install position output
      intro existing hexisting
      rw [hstate] at hexisting
      exact Option.some.inj hexisting.symm
  | none =>
      cases hvalue : context.values position with
      | some output =>
          rw [resolveDeferredPositionValue_of_deferred_value position context output hstate
            hvalue] at hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hresult
          · simp [hhit] at hresult
            subst result
            exact hvalid.clearPending (.position position)
      | none =>
          rw [resolveDeferredPositionValue_fresh position context hstate hvalue,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hreturn⟩ := hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hreturn
          · simp [hhit] at hreturn
            subst result
            apply hvalid.clearPending_install position output
            intro existing hexisting
            rw [hstate] at hexisting
            contradiction

theorem DeferredContext.ValuesConsistent.of_resolveDeferredPositionValue
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    result.toDeferredContext.ValuesConsistent := by
  intro other output hvalue
  have hstateValues := resolveDeferredPositionValue_preserves_state_values
    position context result hresult
  have horiginal : context.state.values (.position other) = some output := by
    rw [← hstateValues]
    exact hvalue
  by_cases heq : other = position
  · subst other
    have hresolved := resolveDeferredPositionValue_resolves position context result hresult
    unfold DeferredContext.positionValue at hresolved
    rw [hvalue] at hresolved
    have hsame : output = result.output := Option.some.inj hresolved
    rw [hsame]
    exact resolveDeferredPositionValue_installs position context result hresult
  · rw [resolveDeferredPositionValue_preserves_other position other context result heq hresult]
    exact hconsistent other output horiginal

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredChainStart_then_finalize
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (coordinates : List Coordinate) (context : DeferredContext)
    (hmem : Coordinate.chainStart lay tree leafIdx chainIdx ∈ coordinates)
    (hvalid : context.Valid) :
    evalDist (do
        let resolved := resolveDeferredChainStart table
          ⟨lay, tree, leafIdx, chainIdx⟩ context
        (match resolved with
        | none => (pure none : ProbComp (Option DeferredContext))
        | some resolved => finalizeResolvedCoordinates coordinates
            resolved.toDeferredContext table)) =
      evalDist (finalizeResolvedCoordinates coordinates context table) := by
  let coordinate := Coordinate.chainStart lay tree leafIdx chainIdx
  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
  have hcoordinate : index.coordinate = coordinate := rfl
  cases hstate : context.state.values coordinate with
  | some output =>
      have hclean := hvalid.2 coordinate output hstate
      have hresolve : resolveDeferredChainStart table index context = some
          ⟨{ state := context.state.clearPending coordinate,
              values := context.values }, output⟩ := by
        simp [resolveDeferredChainStart, hcoordinate, hstate, hclean]
      change evalDist (match resolveDeferredChainStart table index context with
          | none => (pure none : ProbComp (Option DeferredContext))
          | some resolved => finalizeResolvedCoordinates coordinates
              resolved.toDeferredContext table) = _
      rw [hresolve]
      calc
        evalDist (finalizeResolvedCoordinates coordinates
            { state := context.state.clearPending coordinate
              values := context.values } table) =
            evalDist (finalizeResolvedCoordinates
              (coordinate :: coordinates.erase coordinate)
              { state := context.state.clearPending coordinate
                values := context.values } table) :=
          evalDist_finalizeResolvedCoordinates_move_to_front coordinate coordinates
            { state := context.state.clearPending coordinate
              values := context.values } table hmem
        _ = evalDist (finalizeResolvedCoordinates
              (coordinates.erase coordinate)
              { state := context.state.clearPending coordinate
                values := context.values } table) := by
          rw [finalizeResolvedCoordinates_cons_of_state_value coordinate
            (coordinates.erase coordinate)
            { state := context.state.clearPending coordinate
              values := context.values } table output]
          · simp
          · exact hstate
        _ = evalDist (finalizeResolvedCoordinates
              (coordinate :: coordinates.erase coordinate) context table) := by
          rw [finalizeResolvedCoordinates_cons_of_state_value coordinate
            (coordinates.erase coordinate) context table output hstate]
        _ = evalDist (finalizeResolvedCoordinates coordinates context table) :=
          (evalDist_finalizeResolvedCoordinates_move_to_front coordinate coordinates
            context table hmem).symm
  | none =>
      have hstate' : context.state.values index.coordinate = none := by
        simpa [hcoordinate] using hstate
      change evalDist (match resolveDeferredChainStart table index context with
          | none => (pure none : ProbComp (Option DeferredContext))
          | some resolved => finalizeResolvedCoordinates coordinates
              resolved.toDeferredContext table) = _
      rw [resolveDeferredChainStart_of_missing table index context hstate']
      rw [hcoordinate]
      by_cases hhit : context.state.hitAt coordinate (table index)
      · rw [if_pos hhit]
        simp only
        have hstateConcrete : context.state.values
            (.chainStart lay tree leafIdx chainIdx) = none := by
          simpa [coordinate] using hstate
        have hhitConcrete : context.state.hitAt
            (.chainStart lay tree leafIdx chainIdx)
              (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
          simpa [coordinate, index] using hhit
        have hmove := evalDist_finalizeResolvedCoordinates_move_to_front
          coordinate coordinates context table hmem
        simp only [coordinate] at hmove
        rw [finalizeResolvedCoordinates] at hmove
        simp only [hstateConcrete] at hmove
        rw [resolveDeferredChainStart_of_missing table
          ⟨lay, tree, leafIdx, chainIdx⟩ context hstateConcrete] at hmove
        simp only [pure_bind] at hmove
        simp only [OtsSecretIndex.coordinate] at hmove
        rw [if_pos hhitConcrete] at hmove
        simpa using hmove.symm
      · rw [if_neg hhit]
        simp only
        have hclearedState :
            (context.state.clearPending coordinate).values coordinate = none :=
          hstate
        have hclearedClean :
            ¬(context.state.clearPending coordinate).hitAt coordinate (table index) :=
          not_hitAt_clearPending_self context.state coordinate (table index)
        have hhitConcrete : ¬context.state.hitAt
            (.chainStart lay tree leafIdx chainIdx)
              (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
          simpa [coordinate, index] using hhit
        have hclearedCleanConcrete :
            ¬(context.state.clearPending (.chainStart lay tree leafIdx chainIdx)).hitAt
              (.chainStart lay tree leafIdx chainIdx)
              (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
          exact not_hitAt_clearPending_self context.state
            (.chainStart lay tree leafIdx chainIdx)
            (table ⟨lay, tree, leafIdx, chainIdx⟩)
        calc
          evalDist (finalizeResolvedCoordinates coordinates
              { state := context.state.clearPending coordinate
                values := context.values } table) =
              evalDist (finalizeResolvedCoordinates
                (coordinate :: coordinates.erase coordinate)
                { state := context.state.clearPending coordinate
                  values := context.values } table) :=
            evalDist_finalizeResolvedCoordinates_move_to_front coordinate coordinates
              { state := context.state.clearPending coordinate
                values := context.values } table hmem
          _ = evalDist (finalizeResolvedCoordinates
                (coordinates.erase coordinate)
                { state := context.state.complete coordinate (table index)
                  values := context.values } table) := by
            rw [finalizeResolvedCoordinates_cons_of_missing coordinate
              (coordinates.erase coordinate)
              { state := context.state.clearPending coordinate
                values := context.values } table hclearedState]
            simp [coordinate, index, resolvedCompletionOutput, hclearedCleanConcrete,
              DeferredContext.completeResolved, clearPending_complete_self]
          _ = evalDist (finalizeResolvedCoordinates
                (coordinate :: coordinates.erase coordinate) context table) := by
            rw [finalizeResolvedCoordinates_cons_of_missing coordinate
              (coordinates.erase coordinate) context table hstate]
            simp [coordinate, index, resolvedCompletionOutput, hhitConcrete,
              DeferredContext.completeResolved]
          _ = evalDist (finalizeResolvedCoordinates coordinates context table) :=
            (evalDist_finalizeResolvedCoordinates_move_to_front coordinate coordinates
              context table hmem).symm

theorem DeferredContext.Valid.of_resolveDeferredChainStart
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    result.toDeferredContext.Valid := by
  unfold resolveDeferredChainStart at hresult
  cases hstate : context.state.values index.coordinate with
  | some output =>
      simp only [hstate] at hresult
      by_cases hhit : context.state.hitAt index.coordinate output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hvalid.clearPending index.coordinate
  | none =>
      simp only [hstate] at hresult
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hvalid.clearPending index.coordinate

theorem DeferredContext.ValuesConsistent.of_resolveDeferredChainStart
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    result.toDeferredContext.ValuesConsistent := by
  unfold resolveDeferredChainStart at hresult
  cases hstate : context.state.values index.coordinate with
  | some output =>
      simp only [hstate] at hresult
      by_cases hhit : context.state.hitAt index.coordinate output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hconsistent
  | none =>
      simp only [hstate] at hresult
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hconsistent

theorem DeferredContext.ValuesConsistent.of_resolveDeferredChainPrefix
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps result,
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      result.toDeferredContext.ValuesConsistent
  | 0, hsteps, result, hresult => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      exact hconsistent.of_resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩
        result hresult.symm
  | steps + 1, hsteps, result, hresult => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hmiddle := hconsistent.of_resolveDeferredChainPrefix table lay tree leafIdx
            chainIdx steps (by omega) previous hprevious
          exact hmiddle.of_resolveDeferredPositionValue
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) result (by simpa using hrest)

theorem DeferredContext.ValuesConsistent.of_resolveDeferredChains
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ chains result,
      some result ∈ support
        (resolveDeferredChains table lay tree leafIdx chains context) →
      result.ValuesConsistent
  | [], result, hresult => by
      simp [resolveDeferredChains] at hresult
      subst result
      exact hconsistent
  | chainIdx :: remaining, result, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          have hmiddle := hconsistent.of_resolveDeferredChainPrefix table lay tree leafIdx
            chainIdx (chainLength - 1) (by omega) resolved hresolved
          exact hmiddle.of_resolveDeferredChains table lay tree leafIdx remaining result
            (by simpa using hrest)

theorem DeferredContext.ValuesConsistent.of_resolveDeferredOtsLeaf
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    result.toDeferredContext.ValuesConsistent := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      have hmiddle := hconsistent.of_resolveDeferredChains table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
      exact hmiddle.of_resolveDeferredPositionValue (.leaf lay tree leafIdx) result
        (by simpa using hrest)

theorem DeferredContext.ValuesConsistent.of_resolveDeferredTreeNode
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel result,
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      result.toDeferredContext.ValuesConsistent
  | 0, nodeIdx, hlevel, result, hresult =>
      hconsistent.of_resolveDeferredOtsLeaf table lay tree (leafOfNat nodeIdx) result hresult
  | level + 1, nodeIdx, hlevel, result, hresult => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hleftConsistent := hconsistent.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) left hleft
              have hrightConsistent := hleftConsistent.of_resolveDeferredTreeNode table lay tree
                level (2 * nodeIdx + 1) (by omega) right hright
              exact hrightConsistent.of_resolveDeferredPositionValue
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) result
                (by simpa using hafterRight)

theorem DeferredContext.ValuesConsistent.of_resolveDeferredPosition
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    result.toDeferredContext.ValuesConsistent := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact hconsistent.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) result hresult
  | leaf lay tree leafIdx =>
      exact hconsistent.of_resolveDeferredOtsLeaf table lay tree leafIdx result hresult
  | node lay tree level nodeIdx =>
      exact hconsistent.of_resolveDeferredTreeNode table lay tree (level.val + 1) nodeIdx
        (by have := level.isLt; omega) result hresult
  | ftsLeaf index tree leafIdx =>
      exact hconsistent.of_resolveDeferredPositionValue (.ftsLeaf index tree leafIdx) result
        hresult
  | ftsNode index tree level nodeIdx =>
      exact hconsistent.of_resolveDeferredPositionValue (.ftsNode index tree level nodeIdx) result
        hresult
  | ftsRoots index =>
      exact hconsistent.of_resolveDeferredPositionValue (.ftsRoots index) result hresult
theorem DeferredContext.Valid.of_resolveDeferredChainPrefix
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps result,
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      result.toDeferredContext.Valid
  | 0, hsteps, result, hresult => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      exact hvalid.of_resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩
        result hresult.symm
  | steps + 1, hsteps, result, hresult => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hmiddle := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
            steps (by omega) previous hprevious
          exact hmiddle.of_resolveDeferredPositionValue
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) result (by simpa using hrest)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredChainPrefix_then_finalize
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (coordinates : List Coordinate) (context : DeferredContext)
    (hvalid : context.Valid)
    (hstart : Coordinate.chainStart lay tree leafIdx chainIdx ∈ coordinates)
    (hpositions : ∀ step : ChainStep, step.val < chainLength - 1 →
      Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ coordinates) :
    ∀ steps hsteps,
      evalDist (do
          let resolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
            steps hsteps context
          (match resolved with
          | none => (pure none : ProbComp (Option DeferredContext))
          | some resolved => finalizeResolvedCoordinates coordinates
              resolved.toDeferredContext table)) =
        evalDist (finalizeResolvedCoordinates coordinates context table)
  | 0, hsteps => by
      simpa [resolveDeferredChainPrefix] using
        evalDist_resolveDeferredChainStart_then_finalize table lay tree leafIdx chainIdx
          coordinates context hstart hvalid
  | steps + 1, hsteps => by
      rw [resolveDeferredChainPrefix]
      simp only [bind_assoc]
      calc
        _ =
          evalDist
            (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps (by omega) context
              >>= fun previousOption =>
                match previousOption with
                | none => pure none
                | some previous => finalizeResolvedCoordinates coordinates
                    previous.toDeferredContext table) := by
          apply evalDist_bind_congr
          intro previousOption hprevious
          cases previousOption with
          | none => rfl
          | some previous =>
              have hmiddle := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx
                chainIdx steps (by omega) previous hprevious
              exact evalDist_resolveDeferredPositionValue_then_finalize
                (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
                coordinates previous.toDeferredContext table
                (hpositions ⟨steps, by omega⟩ (by omega))
                (fun output hvalue => ⟨hmiddle.1 _ output hvalue,
                  hmiddle.2 _ output hvalue⟩)
        _ = evalDist (finalizeResolvedCoordinates coordinates context table) :=
          evalDist_resolveDeferredChainPrefix_then_finalize table lay tree leafIdx chainIdx
            coordinates context hvalid hstart hpositions steps (by omega)

theorem DeferredContext.Valid.of_resolveDeferredChains
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ chains result,
      some result ∈ support
        (resolveDeferredChains table lay tree leafIdx chains context) →
      result.Valid
  | [], result, hresult => by
      simp [resolveDeferredChains] at hresult
      subst result
      exact hvalid
  | chainIdx :: remaining, result, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          have hmiddle := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
            (chainLength - 1) (by omega) resolved hresolved
          exact hmiddle.of_resolveDeferredChains table lay tree leafIdx remaining result
            (by simpa using hrest)

theorem DeferredContext.Valid.of_resolveDeferredOtsLeaf
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    result.toDeferredContext.Valid := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      have hmiddle := hvalid.of_resolveDeferredChains table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
      exact hmiddle.of_resolveDeferredPositionValue (.leaf lay tree leafIdx) result
        (by simpa using hrest)

theorem DeferredContext.Valid.of_resolveDeferredTreeNode
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel result,
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      result.toDeferredContext.Valid
  | 0, nodeIdx, hlevel, result, hresult =>
      hvalid.of_resolveDeferredOtsLeaf table lay tree (leafOfNat nodeIdx) result hresult
  | level + 1, nodeIdx, hlevel, result, hresult => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hleftValid := hvalid.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) left hleft
              have hrightValid := hleftValid.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx + 1) (by omega) right hright
              exact hrightValid.of_resolveDeferredPositionValue
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) result
                (by simpa using hafterRight)

theorem DeferredContext.Valid.of_resolveDeferredPosition
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    result.toDeferredContext.Valid := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) result hresult
  | leaf lay tree leafIdx =>
      exact hvalid.of_resolveDeferredOtsLeaf table lay tree leafIdx result hresult
  | node lay tree level nodeIdx =>
      exact hvalid.of_resolveDeferredTreeNode table lay tree (level.val + 1) nodeIdx
        (by have := level.isLt; omega) result hresult
  | ftsLeaf index tree leafIdx =>
      exact hvalid.of_resolveDeferredPositionValue (.ftsLeaf index tree leafIdx) result hresult
  | ftsNode index tree level nodeIdx =>
      exact hvalid.of_resolveDeferredPositionValue (.ftsNode index tree level nodeIdx) result
        hresult
  | ftsRoots index =>
      exact hvalid.of_resolveDeferredPositionValue (.ftsRoots index) result hresult

theorem resolveDeferredChains_preserves_state_values
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ chains context result,
      some result ∈ support
        (resolveDeferredChains table lay tree leafIdx chains context) →
      result.state.values = context.state.values
  | [], context, result, hresult => by
      simp [resolveDeferredChains] at hresult
      subst result
      rfl
  | chainIdx :: remaining, context, result, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          exact (resolveDeferredChains_preserves_state_values table lay tree leafIdx remaining
            resolved.toDeferredContext result (by simpa using hrest)).trans
            (resolveDeferredChainPrefix_preserves_state_values table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context resolved hresolved)

theorem resolveDeferredOtsLeaf_preserves_state_values
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    result.state.values = context.state.values := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      exact (resolveDeferredPositionValue_preserves_state_values (.leaf lay tree leafIdx)
        chains result (by simpa using hrest)).trans
        (resolveDeferredChains_preserves_state_values table lay tree leafIdx
          (List.ofFn fun chainIdx : ChainIndex => chainIdx) context chains hchains)

theorem resolveDeferredTreeNode_preserves_state_values
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel context result,
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      result.state.values = context.state.values
  | 0, nodeIdx, hlevel, context, result, hresult =>
      resolveDeferredOtsLeaf_preserves_state_values table lay tree (leafOfNat nodeIdx)
        context result hresult
  | level + 1, nodeIdx, hlevel, context, result, hresult => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              exact (resolveDeferredPositionValue_preserves_state_values
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
                right.toDeferredContext result (by simpa using hafterRight)).trans
                ((resolveDeferredTreeNode_preserves_state_values table lay tree level
                  (2 * nodeIdx + 1) (by omega) left.toDeferredContext right hright).trans
                  (resolveDeferredTreeNode_preserves_state_values table lay tree level
                    (2 * nodeIdx) (by omega) context left hleft))

theorem resolveDeferredPosition_preserves_state_values
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    result.state.values = context.state.values := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact resolveDeferredChainPrefix_preserves_state_values table lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) context result hresult
  | leaf lay tree leafIdx =>
      exact resolveDeferredOtsLeaf_preserves_state_values table lay tree leafIdx context result
        hresult
  | node lay tree level nodeIdx =>
      exact resolveDeferredTreeNode_preserves_state_values table lay tree (level.val + 1)
        nodeIdx (by have := level.isLt; omega) context result hresult
  | ftsLeaf index tree leafIdx =>
      exact resolveDeferredPositionValue_preserves_state_values (.ftsLeaf index tree leafIdx)
        context result hresult
  | ftsNode index tree level nodeIdx =>
      exact resolveDeferredPositionValue_preserves_state_values (.ftsNode index tree level nodeIdx)
        context result hresult
  | ftsRoots index =>
      exact resolveDeferredPositionValue_preserves_state_values (.ftsRoots index) context result
        hresult

theorem resolveDeferredChainPrefix_pending_subset
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps context result,
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      result.state.pending ⊆ context.state.pending
  | 0, hsteps, context, result, hresult => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      unfold resolveDeferredChainStart at hresult
      cases hstate : context.state.values (.chainStart lay tree leafIdx chainIdx) with
      | none =>
          simp only [OtsSecretIndex.coordinate, hstate] at hresult
          split at hresult <;> simp_all [LazyRevealProbe.State.clearPending,
            LazyRevealProbe.State.pendingAway]
      | some output =>
          simp only [OtsSecretIndex.coordinate, hstate] at hresult
          split at hresult <;> simp_all [LazyRevealProbe.State.clearPending,
            LazyRevealProbe.State.pendingAway]
  | steps + 1, hsteps, context, result, hresult => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hprefix := resolveDeferredChainPrefix_pending_subset table lay tree leafIdx
            chainIdx steps (by omega) context previous hprevious
          have hstep := resolveDeferredPositionValue_pending
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
            previous.toDeferredContext result (by simpa using hrest)
          intro entry hentry
          apply hprefix
          rw [hstep] at hentry
          exact (Finset.mem_filter.1 hentry).1

theorem resolveDeferredChains_pending_subset
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ chains context result,
      some result ∈ support (resolveDeferredChains table lay tree leafIdx chains context) →
      result.state.pending ⊆ context.state.pending
  | [], context, result, hresult => by
      simp [resolveDeferredChains] at hresult
      subst result
      exact Finset.Subset.rfl
  | chainIdx :: remaining, context, result, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          exact (resolveDeferredChains_pending_subset table lay tree leafIdx remaining
            resolved.toDeferredContext result (by simpa using hrest)).trans
              (resolveDeferredChainPrefix_pending_subset table lay tree leafIdx chainIdx
                (chainLength - 1) (by omega) context resolved hresolved)

theorem resolveDeferredOtsLeaf_pending_subset
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    result.state.pending ⊆ context.state.pending := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      have hleaf := resolveDeferredPositionValue_pending (.leaf lay tree leafIdx) chains result
        (by simpa using hrest)
      intro entry hentry
      apply resolveDeferredChains_pending_subset table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) context chains hchains
      rw [hleaf] at hentry
      exact (Finset.mem_filter.1 hentry).1

theorem resolveDeferredTreeNode_pending_subset
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel context result,
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      result.state.pending ⊆ context.state.pending
  | 0, nodeIdx, hlevel, context, result, hresult =>
      resolveDeferredOtsLeaf_pending_subset table lay tree (leafOfNat nodeIdx) context result
        hresult
  | level + 1, nodeIdx, hlevel, context, result, hresult => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hnode := resolveDeferredPositionValue_pending
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
                right.toDeferredContext result (by simpa using hafterRight)
              intro entry hentry
              apply (resolveDeferredTreeNode_pending_subset table lay tree level
                (2 * nodeIdx) (by omega) context left hleft)
              apply (resolveDeferredTreeNode_pending_subset table lay tree level
                (2 * nodeIdx + 1) (by omega) left.toDeferredContext right hright)
              rw [hnode] at hentry
              exact (Finset.mem_filter.1 hentry).1

theorem resolveDeferredPosition_pending_subset
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    result.state.pending ⊆ context.state.pending := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact resolveDeferredChainPrefix_pending_subset table lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) context result hresult
  | leaf lay tree leafIdx =>
      exact resolveDeferredOtsLeaf_pending_subset table lay tree leafIdx context result hresult
  | node lay tree level nodeIdx =>
      exact resolveDeferredTreeNode_pending_subset table lay tree (level.val + 1) nodeIdx
        (by have := level.isLt; omega) context result hresult
  | ftsLeaf index tree leafIdx =>
      have hdirect : some result ∈ support
          (resolveDeferredPositionValue (.ftsLeaf index tree leafIdx) context) := by
        simpa [resolveDeferredPosition] using hresult
      rw [resolveDeferredPositionValue_pending (.ftsLeaf index tree leafIdx) context result
        hdirect]
      exact Finset.filter_subset _ _
  | ftsNode index tree level nodeIdx =>
      have hdirect : some result ∈ support
          (resolveDeferredPositionValue (.ftsNode index tree level nodeIdx) context) := by
        simpa [resolveDeferredPosition] using hresult
      rw [resolveDeferredPositionValue_pending (.ftsNode index tree level nodeIdx) context result
        hdirect]
      exact Finset.filter_subset _ _
  | ftsRoots index =>
      have hdirect : some result ∈ support
          (resolveDeferredPositionValue (.ftsRoots index) context) := by
        simpa [resolveDeferredPosition] using hresult
      rw [resolveDeferredPositionValue_pending (.ftsRoots index) context result hdirect]
      exact Finset.filter_subset _ _

theorem resolveDeferredPosition_pendingAway_subset
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    result.state.pending ⊆ context.state.pendingAway (.position position) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      rw [resolveDeferredPosition, resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hstep := resolveDeferredPositionValue_pending
            (.chain lay tree leafIdx chainIdx step) previous.toDeferredContext result
            (by simpa using hrest)
          intro entry hentry
          rw [hstep] at hentry
          have hparts := Finset.mem_filter.1 hentry
          exact Finset.mem_filter.2 ⟨
            resolveDeferredChainPrefix_pending_subset table lay tree leafIdx chainIdx step.val
              (by have := step.isLt; omega) context previous hprevious hparts.1,
            hparts.2⟩
  | leaf lay tree leafIdx =>
      rw [resolveDeferredPosition, resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
      obtain ⟨chainsOption, hchains, hrest⟩ := hresult
      cases chainsOption with
      | none => simp at hrest
      | some chains =>
          have hleaf := resolveDeferredPositionValue_pending (.leaf lay tree leafIdx) chains
            result (by simpa using hrest)
          intro entry hentry
          rw [hleaf] at hentry
          have hparts := Finset.mem_filter.1 hentry
          exact Finset.mem_filter.2 ⟨
            resolveDeferredChains_pending_subset table lay tree leafIdx
              (List.ofFn fun chainIdx : ChainIndex => chainIdx) context chains hchains hparts.1,
            hparts.2⟩
  | node lay tree level nodeIdx =>
      rw [resolveDeferredPosition, resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hnode := resolveDeferredPositionValue_pending (.node lay tree level nodeIdx)
                right.toDeferredContext result (by simpa [leafOfNat_val] using hafterRight)
              intro entry hentry
              rw [hnode] at hentry
              have hparts := Finset.mem_filter.1 hentry
              apply Finset.mem_filter.2
              refine ⟨?_, hparts.2⟩
              apply resolveDeferredTreeNode_pending_subset table lay tree level.val
                (2 * nodeIdx.val) (by have := level.isLt; omega) context left hleft
              apply resolveDeferredTreeNode_pending_subset table lay tree level.val
                (2 * nodeIdx.val + 1) (by have := level.isLt; omega) left.toDeferredContext
                  right hright
              exact hparts.1
  | ftsLeaf index tree leafIdx =>
      have hdirect : some result ∈ support
          (resolveDeferredPositionValue (.ftsLeaf index tree leafIdx) context) := by
        simpa [resolveDeferredPosition] using hresult
      rw [resolveDeferredPositionValue_pending (.ftsLeaf index tree leafIdx) context result
        hdirect]
  | ftsNode index tree level nodeIdx =>
      have hdirect : some result ∈ support
          (resolveDeferredPositionValue (.ftsNode index tree level nodeIdx) context) := by
        simpa [resolveDeferredPosition] using hresult
      rw [resolveDeferredPositionValue_pending (.ftsNode index tree level nodeIdx) context result
        hdirect]
  | ftsRoots index =>
      have hdirect : some result ∈ support
          (resolveDeferredPositionValue (.ftsRoots index) context) := by
        simpa [resolveDeferredPosition] using hresult
      rw [resolveDeferredPositionValue_pending (.ftsRoots index) context result hdirect]

theorem resolveDeferredReveal_preserves_state_values
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context)) :
    result.state.values = context.state.values := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · apply resolveDeferredPosition_preserves_state_values table position context result
    simpa [resolveDeferredReveal, hresolvable] using hresult
  · apply resolveDeferredPositionValue_preserves_state_values position context result
    simpa [resolveDeferredReveal, hresolvable] using hresult

theorem resolveDeferredReveal_pendingAway_subset
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context)) :
    result.state.pending ⊆ context.state.pendingAway (.position position) := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · apply resolveDeferredPosition_pendingAway_subset table position context result
    simpa [resolveDeferredReveal, hresolvable] using hresult
  · have hdirect : some result ∈ support
        (resolveDeferredPositionValue position context) := by
      simpa [resolveDeferredReveal, hresolvable] using hresult
    rw [resolveDeferredPositionValue_pending position context result hdirect]

theorem resolveDeferredReveal_resolves
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context)) :
    result.toDeferredContext.positionValue position = some result.output := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · apply resolveDeferredPosition_resolves table position context result
    simpa [resolveDeferredReveal, hresolvable] using hresult
  · apply resolveDeferredPositionValue_resolves position context result
    simpa [resolveDeferredReveal, hresolvable] using hresult

theorem DeferredContext.Valid.of_resolveDeferredReveal
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context)) :
    result.toDeferredContext.Valid := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · apply hvalid.of_resolveDeferredPosition table position result
    simpa [resolveDeferredReveal, hresolvable] using hresult
  · apply hvalid.of_resolveDeferredPositionValue position result
    simpa [resolveDeferredReveal, hresolvable] using hresult

theorem DeferredContext.ValuesConsistent.of_resolveDeferredReveal
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredReveal table position context)) :
    result.toDeferredContext.ValuesConsistent := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · apply hconsistent.of_resolveDeferredPosition table position result
    simpa [resolveDeferredReveal, hresolvable] using hresult
  · apply hconsistent.of_resolveDeferredPositionValue position result
    simpa [resolveDeferredReveal, hresolvable] using hresult

theorem DeferredContext.Valid.materialize_position
    {context : DeferredContext} (hvalid : context.Valid)
    (position : Position) (output : HashOutput)
    (hvalue : context.values position = some output) :
    ({ state := context.state.materialize (.position position) output
       values := context.values } : DeferredContext).Valid := by
  constructor
  · intro other candidate hstate
    by_cases heq : other = position
    · subst other
      have hsame : some output = some candidate := by
        simpa [LazyRevealProbe.State.materialize] using hstate
      have hcandidate : output = candidate := Option.some.inj hsame
      subst candidate
      exact hvalue
    · have horiginal : context.state.values (.position other) = some candidate := by
        simpa [LazyRevealProbe.State.materialize, Function.update_of_ne,
          show Coordinate.position other ≠ Coordinate.position position by
            simpa using heq] using hstate
      exact hvalid.1 other candidate horiginal
  · intro coordinate candidate hstate
    by_cases heq : coordinate = .position position
    · subst coordinate
      change ¬(context.state.clearPending (.position position)).hitAt
        (.position position) candidate
      exact not_hitAt_clearPending_self context.state (.position position) candidate
    · have horiginal : context.state.values coordinate = some candidate := by
        simpa [LazyRevealProbe.State.materialize, Function.update_of_ne heq] using hstate
      change ¬(context.state.clearPending (.position position)).hitAt coordinate candidate
      exact (hitAt_clearPending_of_ne context.state (.position position) coordinate candidate
        heq).not.mpr (hvalid.2 coordinate candidate horiginal)

theorem DeferredContext.Valid.materialize_resolved_position
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    ({ state := result.state.materialize (.position position) result.output
       values := result.values } : DeferredContext).Valid := by
  have hresolved := resolveDeferredPosition_resolves table position context result hresult
  have hresultValid := hvalid.of_resolveDeferredPosition table position result hresult
  have hprivate : result.values position = some result.output := by
    unfold DeferredContext.positionValue at hresolved
    cases hstate : result.state.values (.position position) with
    | none => simpa [hstate] using hresolved
    | some output =>
        have hsame : output = result.output := by
          simpa [hstate] using hresolved
        simpa [hsame] using hresultValid.1 position output hstate
  exact hresultValid.materialize_position position result.output hprivate

theorem DeferredContext.Valid.materialize_resolved_position_from_context
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    ({ state := context.state.materialize (.position position) result.output
       values := result.values } : DeferredContext).Valid := by
  have hstateValues := resolveDeferredPosition_preserves_state_values table position context
    result hresult
  have hresultValid := hvalid.of_resolveDeferredPosition table position result hresult
  have htemporary :
      ({ state := context.state, values := result.values } : DeferredContext).Valid := by
    constructor
    · intro other output hvalue
      apply hresultValid.1 other output
      rw [hstateValues]
      exact hvalue
    · exact hvalid.2
  have hprivate : result.values position = some result.output := by
    have hresolved := resolveDeferredPosition_resolves table position context result hresult
    unfold DeferredContext.positionValue at hresolved
    rw [hstateValues] at hresolved
    cases hstate : context.state.values (.position position) with
    | none => simpa [hstate] using hresolved
    | some output =>
        have hsame : output = result.output := by
          simpa [hstate] using hresolved
        simpa [hsame] using hresultValid.1 position output (by
          rw [hstateValues]
          exact hstate)
  exact htemporary.materialize_position position result.output hprivate

theorem DeferredContext.valid_empty :
    ({ state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
       values := emptyDeferredStructuralValues } : DeferredContext).Valid := by
  constructor
  · intro position output hvalue
    simp [LazyRevealProbe.State.empty] at hvalue
  · intro coordinate output hvalue
    simp [LazyRevealProbe.State.empty] at hvalue

theorem DeferredContext.Valid.ensure
    {context : DeferredContext} (hvalid : context.Valid) (coordinate : Coordinate) :
    ({ context with state := context.state.ensure coordinate } : DeferredContext).Valid := by
  constructor
  · exact hvalid.1
  · intro other output hvalue
    change ¬context.state.hitAt other output
    exact hvalid.2 other output hvalue

theorem DeferredContext.Valid.publish
    {context : DeferredContext} (hvalid : context.Valid) (coordinate : Coordinate) :
    ({ context with state := context.state.publish coordinate } : DeferredContext).Valid := by
  constructor
  · exact hvalid.1
  · intro other output hvalue
    change ¬context.state.hitAt other output
    exact hvalid.2 other output hvalue

theorem DeferredContext.Valid.materialize_chainStart
    {context : DeferredContext} (hvalid : context.Valid)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (output : HashOutput) :
    ({ state := context.state.materialize
          (.chainStart lay tree leafIdx chainIdx) output
       values := context.values } : DeferredContext).Valid := by
  let coordinate := Coordinate.chainStart lay tree leafIdx chainIdx
  constructor
  · intro position candidate hstate
    have horiginal : context.state.values (.position position) = some candidate := by
      simpa [coordinate, LazyRevealProbe.State.materialize] using hstate
    exact hvalid.1 position candidate horiginal
  · intro other candidate hstate
    by_cases heq : other = coordinate
    · subst other
      change ¬(context.state.clearPending coordinate).hitAt coordinate candidate
      exact not_hitAt_clearPending_self context.state coordinate candidate
    · have horiginal : context.state.values other = some candidate := by
        simpa [coordinate, LazyRevealProbe.State.materialize,
          Function.update_of_ne heq] using hstate
      change ¬(context.state.clearPending coordinate).hitAt other candidate
      exact (hitAt_clearPending_of_ne context.state coordinate other candidate heq).not.mpr
        (hvalid.2 other candidate horiginal)

theorem DeferredContext.Valid.materialize_resolved_chainStart
    {context : DeferredContext} (hvalid : context.Valid)
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    ({ state := result.state.materialize index.coordinate result.output
       values := result.values } : DeferredContext).Valid := by
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  have hresultValid := hvalid.of_resolveDeferredChainStart table
    ⟨lay, tree, leafIdx, chainIdx⟩ result hresult
  exact hresultValid.materialize_chainStart lay tree leafIdx chainIdx result.output

def projectDeferredState : Option DeferredContext →
    Option (LazyRevealProbe.State Coordinate) :=
  Option.map DeferredContext.state

set_option maxRecDepth 100000 in
theorem evalDist_map_finalizeResolvedCoordinates_congr_values
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate)
    (left right : DeferredStructuralValues) (table : OtsSecretIndex → HashOutput)
    (hagrees : ∀ position : Position, Coordinate.position position ∈ coordinates →
      left position = right position) :
    evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates ⟨state, left⟩ table) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates ⟨state, right⟩ table) := by
  induction coordinates generalizing state left right with
  | nil => simp [finalizeResolvedCoordinates, projectDeferredState]
  | cons coordinate remaining ih =>
      cases hstate : state.values coordinate with
      | some output =>
          rw [finalizeResolvedCoordinates_cons_of_state_value coordinate remaining
            ⟨state, left⟩ table output hstate,
            finalizeResolvedCoordinates_cons_of_state_value coordinate remaining
              ⟨state, right⟩ table output hstate]
          exact ih (state.clearPending coordinate) left right (by
            intro position hmem
            exact hagrees position (List.mem_cons_of_mem coordinate hmem))
      | none =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              have hstate' : state.values index.coordinate = none := by
                simpa [index, OtsSecretIndex.coordinate] using hstate
              rw [finalizeResolvedCoordinates, finalizeResolvedCoordinates]
              simp only [hstate]
              rw [resolveDeferredChainStart_of_missing table index ⟨state, left⟩ hstate',
                resolveDeferredChainStart_of_missing table index ⟨state, right⟩ hstate']
              simp only [map_eq_bind_pure_comp, pure_bind]
              simp only [index, OtsSecretIndex.coordinate]
              by_cases hhit : state.hitAt index.coordinate (table index)
              · have hhit' : state.hitAt (.chainStart lay tree leafIdx chainIdx)
                    (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                  simpa [index, OtsSecretIndex.coordinate] using hhit
                rw [if_pos hhit', if_pos hhit']
              · simp only [index, OtsSecretIndex.coordinate] at hhit
                rw [if_neg hhit, if_neg hhit]
                simp only
                rw [clearPending_complete_self]
                exact ih (state.complete (.chainStart lay tree leafIdx chainIdx) (table index))
                  left right (by
                    intro position hmem
                    exact hagrees position (List.mem_cons_of_mem _ hmem))
          | position position =>
              have hprivate : left position = right position :=
                hagrees position (by simp)
              cases hleft : left position with
              | some output =>
                  have hright : right position = some output := by
                    rw [← hprivate]
                    exact hleft
                  rw [finalizeResolvedCoordinates_cons_position_of_deferred_value position
                    remaining ⟨state, left⟩ table output hstate hleft,
                    finalizeResolvedCoordinates_cons_position_of_deferred_value position
                      remaining ⟨state, right⟩ table output hstate hright]
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih (state.complete (.position position) output) left right (by
                      intro other hmem
                      exact hagrees other (List.mem_cons_of_mem _ hmem))
              | none =>
                  have hright : right position = none := by
                    rw [← hprivate]
                    exact hleft
                  rw [finalizeResolvedCoordinates_cons_position_fresh position remaining
                    ⟨state, left⟩ table hstate hleft,
                    finalizeResolvedCoordinates_cons_position_fresh position remaining
                      ⟨state, right⟩ table hstate hright]
                  simp only [map_eq_bind_pure_comp, bind_assoc]
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro output
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    apply ih (state.complete (.position position) output)
                      (left.install position output) (right.install position output)
                    intro other hmem
                    by_cases heq : other = position
                    · subst other
                      simp [DeferredStructuralValues.install]
                    · simp [DeferredStructuralValues.install, heq,
                        hagrees other (List.mem_cons_of_mem _ hmem)]

theorem evalDist_map_finalizeResolvedCoordinates_install_of_not_mem
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate)
    (values : DeferredStructuralValues) (table : OtsSecretIndex → HashOutput)
    (position : Position) (output : HashOutput)
    (hnotMem : Coordinate.position position ∉ coordinates) :
    evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates
          ⟨state, values.install position output⟩ table) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates ⟨state, values⟩ table) := by
  apply evalDist_map_finalizeResolvedCoordinates_congr_values
  intro other hmem
  have hne : other ≠ position := by
    intro heq
    subst other
    exact hnotMem hmem
  simp [DeferredStructuralValues.install, hne]

set_option maxRecDepth 100000 in
theorem evalDist_map_resolveDeferredPositionValue_then_finalize_of_not_mem
    (position : Position) (coordinates : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hnotMem : Coordinate.position position ∉ coordinates)
    (hstate : context.state.values (.position position) = none)
    (hclear : context.state.clearPending (.position position) = context.state) :
    evalDist (do
        let resolved ← resolveDeferredPositionValue position context
        match resolved with
        | none => (pure none : ProbComp
            (Option (LazyRevealProbe.State Coordinate)))
        | some resolved => projectDeferredState <$>
            finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates context table) := by
  have hclean : ∀ output,
      ¬context.state.hitAt (.position position) output := by
    intro output
    rw [← hclear]
    exact not_hitAt_clearPending_self context.state (.position position) output
  cases hvalue : context.values position with
  | some output =>
      rw [resolveDeferredPositionValue_of_deferred_value position context output hstate hvalue,
        if_neg (hclean output)]
      simp only [pure_bind, hclear]
  | none =>
      rw [resolveDeferredPositionValue_fresh position context hstate hvalue]
      simp only [bind_assoc]
      have hpointwise : ∀ output,
          evalDist (projectDeferredState <$>
              finalizeResolvedCoordinates coordinates
                ⟨context.state, context.values.install position output⟩ table) =
            evalDist (projectDeferredState <$>
              finalizeResolvedCoordinates coordinates context table) := by
        intro output
        exact evalDist_map_finalizeResolvedCoordinates_install_of_not_mem coordinates
          context.state context.values table position output hnotMem
      calc
        _ = evalDist (LazyRevealProbe.sampleHashOutput >>= fun output =>
              projectDeferredState <$>
                finalizeResolvedCoordinates coordinates
                  ⟨context.state, context.values.install position output⟩ table) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          simp [hclean output, hclear]
        _ = evalDist (LazyRevealProbe.sampleHashOutput >>= fun _ =>
              projectDeferredState <$>
                finalizeResolvedCoordinates coordinates context table) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          exact hpointwise
        _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
          LazyRevealProbe.sampleHashOutput (by
            simp [LazyRevealProbe.sampleHashOutput])
          (projectDeferredState <$>
            finalizeResolvedCoordinates coordinates context table)

theorem evalDist_map_resolveDeferredChainStart_then_finalize_of_not_mem
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (coordinates : List Coordinate) (context : DeferredContext)
    (hstate : context.state.values index.coordinate = none)
    (hclear : context.state.clearPending index.coordinate = context.state) :
    evalDist (do
        let resolved := resolveDeferredChainStart table index context
        match resolved with
        | none => (pure none : ProbComp
            (Option (LazyRevealProbe.State Coordinate)))
        | some resolved => projectDeferredState <$>
            finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates context table) := by
  have hclean : ¬context.state.hitAt index.coordinate (table index) := by
    rw [← hclear]
    exact not_hitAt_clearPending_self context.state index.coordinate (table index)
  rw [resolveDeferredChainStart_of_missing table index context hstate, if_neg hclean]
  simp [hclear]

def PendingCovered (coordinates : List Coordinate) (context : DeferredContext) : Prop :=
  ∀ entry, entry ∈ context.state.pending → entry.1 ∈ coordinates

theorem PendingCovered.clearPending
    {coordinates : List Coordinate} {context : DeferredContext}
    (hcovered : PendingCovered coordinates context) (coordinate : Coordinate) :
    PendingCovered coordinates
      { context with state := context.state.clearPending coordinate } := by
  intro entry hentry
  apply hcovered entry
  simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway] at hentry
  exact hentry.1

theorem clearPending_eq_self_of_pendingCovered_not_mem
    (coordinates : List Coordinate) (context : DeferredContext)
    (hcovered : PendingCovered coordinates context)
    (coordinate : Coordinate) (hnotMem : coordinate ∉ coordinates) :
    context.state.clearPending coordinate = context.state := by
  rcases context with ⟨state, values⟩
  rcases state with ⟨pending, stateValues, revealed, ensured⟩
  simp only [LazyRevealProbe.State.clearPending]
  congr 1
  apply Finset.filter_eq_self.2
  intro entry hentry
  simp only [ne_eq]
  intro heq
  exact hnotMem (heq ▸ hcovered entry hentry)

theorem PendingCovered.of_resolveDeferredPositionValue
    {coordinates : List Coordinate} {context : DeferredContext}
    (hcovered : PendingCovered coordinates context)
    (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    PendingCovered coordinates result.toDeferredContext := by
  cases hstate : context.state.values (.position position) with
  | some output =>
      rw [resolveDeferredPositionValue_of_state_value position context output hstate] at hresult
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hcovered.clearPending (.position position)
  | none =>
      cases hvalue : context.values position with
      | some output =>
          rw [resolveDeferredPositionValue_of_deferred_value position context output hstate
            hvalue] at hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hresult
          · simp [hhit] at hresult
            subst result
            exact hcovered.clearPending (.position position)
      | none =>
          rw [resolveDeferredPositionValue_fresh position context hstate hvalue,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hreturn⟩ := hresult
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hreturn
          · simp [hhit] at hreturn
            subst result
            exact hcovered.clearPending (.position position)

theorem PendingCovered.of_resolveDeferredChainStart
    {coordinates : List Coordinate} {context : DeferredContext}
    (hcovered : PendingCovered coordinates context)
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    PendingCovered coordinates result.toDeferredContext := by
  unfold resolveDeferredChainStart at hresult
  cases hstate : context.state.values index.coordinate with
  | some output =>
      simp only [hstate] at hresult
      by_cases hhit : context.state.hitAt index.coordinate output
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hcovered.clearPending index.coordinate
  | none =>
      simp only [hstate] at hresult
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hhit] at hresult
      · simp [hhit] at hresult
        subst result
        exact hcovered.clearPending index.coordinate

theorem PendingCovered.of_resolveDeferredChainPrefix
    {coordinates : List Coordinate} {context : DeferredContext}
    (hcovered : PendingCovered coordinates context)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) : ∀ steps hsteps result,
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      PendingCovered coordinates result.toDeferredContext
  | 0, hsteps, result, hresult => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      exact hcovered.of_resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩
        result hresult.symm
  | steps + 1, hsteps, result, hresult => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hmiddle := hcovered.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
            steps (by omega) previous hprevious
          exact hmiddle.of_resolveDeferredPositionValue
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) result (by simpa using hrest)

theorem PendingCovered.of_resolveDeferredChains
    {coordinates : List Coordinate} {context : DeferredContext}
    (hcovered : PendingCovered coordinates context)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) : ∀ chains result,
      some result ∈ support
        (resolveDeferredChains table lay tree leafIdx chains context) →
      PendingCovered coordinates result
  | [], result, hresult => by
      simp [resolveDeferredChains] at hresult
      subst result
      exact hcovered
  | chainIdx :: remaining, result, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          have hmiddle := hcovered.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
            (chainLength - 1) (by omega) resolved hresolved
          exact hmiddle.of_resolveDeferredChains table lay tree leafIdx remaining result
            (by simpa using hrest)

theorem PendingCovered.of_resolveDeferredOtsLeaf
    {coordinates : List Coordinate} {context : DeferredContext}
    (hcovered : PendingCovered coordinates context)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    PendingCovered coordinates result.toDeferredContext := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      have hmiddle := hcovered.of_resolveDeferredChains table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
      exact hmiddle.of_resolveDeferredPositionValue (.leaf lay tree leafIdx) result
        (by simpa using hrest)

theorem PendingCovered.of_resolveDeferredTreeNode
    {coordinates : List Coordinate} {context : DeferredContext}
    (hcovered : PendingCovered coordinates context)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel result,
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      PendingCovered coordinates result.toDeferredContext
  | 0, nodeIdx, hlevel, result, hresult =>
      hcovered.of_resolveDeferredOtsLeaf table lay tree (leafOfNat nodeIdx) result hresult
  | level + 1, nodeIdx, hlevel, result, hresult => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hleftCovered := hcovered.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) left hleft
              have hrightCovered := hleftCovered.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx + 1) (by omega) right hright
              exact hrightCovered.of_resolveDeferredPositionValue
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) result
                (by simpa using hafterRight)

theorem PendingCovered.of_resolveDeferredPosition
    {coordinates : List Coordinate} {context : DeferredContext}
    (hcovered : PendingCovered coordinates context)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPosition table position context)) :
    PendingCovered coordinates result.toDeferredContext := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact hcovered.of_resolveDeferredChainPrefix table lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) result hresult
  | leaf lay tree leafIdx =>
      exact hcovered.of_resolveDeferredOtsLeaf table lay tree leafIdx result hresult
  | node lay tree level nodeIdx =>
      exact hcovered.of_resolveDeferredTreeNode table lay tree (level.val + 1) nodeIdx
        (by have := level.isLt; omega) result hresult
  | ftsLeaf index tree leafIdx =>
      exact hcovered.of_resolveDeferredPositionValue (.ftsLeaf index tree leafIdx) result hresult
  | ftsNode index tree level nodeIdx =>
      exact hcovered.of_resolveDeferredPositionValue (.ftsNode index tree level nodeIdx) result
        hresult
  | ftsRoots index =>
      exact hcovered.of_resolveDeferredPositionValue (.ftsRoots index) result hresult

set_option maxRecDepth 100000 in
theorem evalDist_map_resolveDeferredPositionValue_then_finalize
    (position : Position) (coordinates : List Coordinate)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcovered : PendingCovered coordinates context) :
    evalDist (do
        let resolved ← resolveDeferredPositionValue position context
        match resolved with
        | none => (pure none : ProbComp
            (Option (LazyRevealProbe.State Coordinate)))
        | some resolved => projectDeferredState <$>
            finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates context table) := by
  by_cases hmem : Coordinate.position position ∈ coordinates
  · have hbase := evalDist_resolveDeferredPositionValue_then_finalize position coordinates
      context table hmem (fun output hvalue =>
        ⟨hvalid.1 position output hvalue, hvalid.2 (.position position) output hvalue⟩)
    calc
      _ = evalDist (projectDeferredState <$> (do
          let resolved ← resolveDeferredPositionValue position context
          (match resolved with
          | none => (pure none : ProbComp (Option DeferredContext))
          | some resolved => finalizeResolvedCoordinates coordinates
              resolved.toDeferredContext table))) := by
        simp only [evalDist_bind, evalDist_map, map_bind]
        congr 1
        funext resolved
        cases resolved <;> simp [projectDeferredState]
      _ = evalDist (projectDeferredState <$>
          finalizeResolvedCoordinates coordinates context table) := by
        rw [evalDist_map, evalDist_map, hbase]
  · have hclear := clearPending_eq_self_of_pendingCovered_not_mem coordinates context
      hcovered (.position position) hmem
    cases hstate : context.state.values (.position position) with
    | none =>
        exact evalDist_map_resolveDeferredPositionValue_then_finalize_of_not_mem position
          coordinates context table hmem hstate hclear
    | some output =>
        have hprivate := hvalid.1 position output hstate
        have hclean := hvalid.2 (.position position) output hstate
        rw [resolveDeferredPositionValue_of_state_value position context output hstate,
          if_neg hclean]
        simp only [pure_bind, hclear]
        have hinstall : context.values.install position output = context.values := by
          funext other
          by_cases heq : other = position
          · subst other
            simp [DeferredStructuralValues.install, hprivate]
          · simp [DeferredStructuralValues.install, heq]
        simp [hinstall]

set_option maxRecDepth 100000 in
theorem evalDist_map_resolveDeferredChainStart_then_finalize
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (coordinates : List Coordinate) (context : DeferredContext)
    (hvalid : context.Valid) (hcovered : PendingCovered coordinates context) :
    evalDist (match resolveDeferredChainStart table index context with
        | none => (pure none : ProbComp
            (Option (LazyRevealProbe.State Coordinate)))
        | some resolved => projectDeferredState <$>
            finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates context table) := by
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  let coordinate := Coordinate.chainStart lay tree leafIdx chainIdx
  by_cases hmem : coordinate ∈ coordinates
  · have hbase := evalDist_resolveDeferredChainStart_then_finalize table lay tree leafIdx
      chainIdx coordinates context hmem hvalid
    calc
      _ = evalDist (projectDeferredState <$> (match
          resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
          | none => (pure none : ProbComp (Option DeferredContext))
          | some resolved => finalizeResolvedCoordinates coordinates
              resolved.toDeferredContext table)) := by
        cases resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context <;>
          simp [projectDeferredState]
      _ = evalDist (projectDeferredState <$>
          finalizeResolvedCoordinates coordinates context table) := by
        rw [evalDist_map, evalDist_map, hbase]
  · have hclear := clearPending_eq_self_of_pendingCovered_not_mem coordinates context
      hcovered coordinate hmem
    cases hstate : context.state.values coordinate with
    | none =>
        exact evalDist_map_resolveDeferredChainStart_then_finalize_of_not_mem table
          ⟨lay, tree, leafIdx, chainIdx⟩ coordinates context
          (by simpa [coordinate, OtsSecretIndex.coordinate] using hstate)
          (by simpa [coordinate, OtsSecretIndex.coordinate] using hclear)
    | some output =>
        have hclean := hvalid.2 coordinate output hstate
        unfold resolveDeferredChainStart
        simp [coordinate, OtsSecretIndex.coordinate, hstate, hclean, hclear]

set_option maxRecDepth 100000 in
theorem evalDist_map_resolveDeferredChainPrefix_then_finalize
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (coordinates : List Coordinate) (context : DeferredContext)
    (hvalid : context.Valid) (hcovered : PendingCovered coordinates context) :
    ∀ steps hsteps,
      evalDist (do
          let resolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
            steps hsteps context
          match resolved with
          | none => (pure none : ProbComp
              (Option (LazyRevealProbe.State Coordinate)))
          | some resolved => projectDeferredState <$>
              finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) =
        evalDist (projectDeferredState <$>
          finalizeResolvedCoordinates coordinates context table)
  | 0, hsteps => by
      simpa [resolveDeferredChainPrefix] using
        evalDist_map_resolveDeferredChainStart_then_finalize table
          ⟨lay, tree, leafIdx, chainIdx⟩ coordinates context hvalid hcovered
  | steps + 1, hsteps => by
      rw [resolveDeferredChainPrefix]
      simp only [bind_assoc]
      calc
        _ = evalDist
            (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps (by omega) context
              >>= fun previousOption =>
                match previousOption with
                | none => pure none
                | some previous => projectDeferredState <$>
                    finalizeResolvedCoordinates coordinates previous.toDeferredContext table) := by
          apply evalDist_bind_congr
          intro previousOption hprevious
          cases previousOption with
          | none => rfl
          | some previous =>
              have hmiddleValid := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx
                chainIdx steps (by omega) previous hprevious
              have hmiddleCovered := hcovered.of_resolveDeferredChainPrefix table lay tree leafIdx
                chainIdx steps (by omega) previous hprevious
              exact evalDist_map_resolveDeferredPositionValue_then_finalize
                (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩)
                coordinates previous.toDeferredContext table hmiddleValid hmiddleCovered
        _ = evalDist (projectDeferredState <$>
            finalizeResolvedCoordinates coordinates context table) :=
          evalDist_map_resolveDeferredChainPrefix_then_finalize table lay tree leafIdx chainIdx
            coordinates context hvalid hcovered steps (by omega)

set_option maxRecDepth 100000 in
theorem evalDist_map_resolveDeferredChains_then_finalize
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (coordinates : List Coordinate) :
    ∀ chains context,
      context.Valid → PendingCovered coordinates context →
      evalDist (do
          let resolved ← resolveDeferredChains table lay tree leafIdx chains context
          match resolved with
          | none => (pure none : ProbComp
              (Option (LazyRevealProbe.State Coordinate)))
          | some resolved => projectDeferredState <$>
              finalizeResolvedCoordinates coordinates resolved table) =
        evalDist (projectDeferredState <$>
          finalizeResolvedCoordinates coordinates context table)
  | [], context, hvalid, hcovered => by
      simp [resolveDeferredChains]
  | chainIdx :: remaining, context, hvalid, hcovered => by
      rw [resolveDeferredChains]
      simp only [bind_assoc]
      calc
        _ = evalDist
            (resolveDeferredChainPrefix table lay tree leafIdx chainIdx
                (chainLength - 1) (by omega) context >>= fun resolvedOption =>
              match resolvedOption with
              | none => pure none
              | some resolved => projectDeferredState <$>
                  finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) := by
          apply evalDist_bind_congr
          intro resolvedOption hresolved
          cases resolvedOption with
          | none => rfl
          | some resolved =>
              have hmiddleValid := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx
                chainIdx (chainLength - 1) (by omega) resolved hresolved
              have hmiddleCovered := hcovered.of_resolveDeferredChainPrefix table lay tree leafIdx
                chainIdx (chainLength - 1) (by omega) resolved hresolved
              exact evalDist_map_resolveDeferredChains_then_finalize table lay tree leafIdx
                coordinates remaining resolved.toDeferredContext hmiddleValid hmiddleCovered
        _ = evalDist (projectDeferredState <$>
            finalizeResolvedCoordinates coordinates context table) :=
          evalDist_map_resolveDeferredChainPrefix_then_finalize table lay tree leafIdx chainIdx
            coordinates context hvalid hcovered (chainLength - 1) (by omega)

set_option maxRecDepth 100000 in
theorem evalDist_map_resolveDeferredOtsLeaf_then_finalize
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (coordinates : List Coordinate) (context : DeferredContext)
    (hvalid : context.Valid) (hcovered : PendingCovered coordinates context) :
    evalDist (do
        let resolved ← resolveDeferredOtsLeaf table lay tree leafIdx context
        match resolved with
        | none => (pure none : ProbComp
            (Option (LazyRevealProbe.State Coordinate)))
        | some resolved => projectDeferredState <$>
            finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates context table) := by
  rw [resolveDeferredOtsLeaf]
  simp only [bind_assoc]
  calc
    _ = evalDist
        (resolveDeferredChains table lay tree leafIdx
            (List.ofFn fun chainIdx : ChainIndex => chainIdx) context >>= fun chainsOption =>
          match chainsOption with
          | none => pure none
          | some chains => projectDeferredState <$>
              finalizeResolvedCoordinates coordinates chains table) := by
      apply evalDist_bind_congr
      intro chainsOption hchains
      cases chainsOption with
      | none => rfl
      | some chains =>
          have hmiddleValid := hvalid.of_resolveDeferredChains table lay tree leafIdx
            (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
          have hmiddleCovered := hcovered.of_resolveDeferredChains table lay tree leafIdx
            (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
          exact evalDist_map_resolveDeferredPositionValue_then_finalize
            (.leaf lay tree leafIdx) coordinates chains table hmiddleValid hmiddleCovered
    _ = evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates context table) :=
      evalDist_map_resolveDeferredChains_then_finalize table lay tree leafIdx coordinates
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) context hvalid hcovered

set_option maxRecDepth 100000 in
theorem evalDist_map_resolveDeferredTreeNode_then_finalize
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (coordinates : List Coordinate) : ∀ level nodeIdx hlevel context,
      context.Valid → PendingCovered coordinates context →
      evalDist (do
          let resolved ← resolveDeferredTreeNode table lay tree level nodeIdx hlevel context
          match resolved with
          | none => (pure none : ProbComp
              (Option (LazyRevealProbe.State Coordinate)))
          | some resolved => projectDeferredState <$>
              finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) =
        evalDist (projectDeferredState <$>
          finalizeResolvedCoordinates coordinates context table)
  | 0, nodeIdx, hlevel, context, hvalid, hcovered => by
      simpa [resolveDeferredTreeNode] using
        evalDist_map_resolveDeferredOtsLeaf_then_finalize table lay tree (leafOfNat nodeIdx)
          coordinates context hvalid hcovered
  | level + 1, nodeIdx, hlevel, context, hvalid, hcovered => by
      rw [resolveDeferredTreeNode]
      simp only [bind_assoc]
      calc
        _ = evalDist
            (resolveDeferredTreeNode table lay tree level (2 * nodeIdx) (by omega) context
              >>= fun leftOption =>
                match leftOption with
                | none => pure none
                | some left => projectDeferredState <$>
                    finalizeResolvedCoordinates coordinates left.toDeferredContext table) := by
          apply evalDist_bind_congr
          intro leftOption hleft
          cases leftOption with
          | none => rfl
          | some left =>
              simp only [bind_assoc]
              have hleftValid := hvalid.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) left hleft
              have hleftCovered := hcovered.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) left hleft
              calc
                _ = evalDist
                    (resolveDeferredTreeNode table lay tree level (2 * nodeIdx + 1)
                        (by omega) left.toDeferredContext >>= fun rightOption =>
                      match rightOption with
                      | none => pure none
                      | some right => projectDeferredState <$>
                          finalizeResolvedCoordinates coordinates right.toDeferredContext table) := by
                    apply evalDist_bind_congr
                    intro rightOption hright
                    cases rightOption with
                    | none => rfl
                    | some right =>
                        have hrightValid := hleftValid.of_resolveDeferredTreeNode table lay tree
                          level (2 * nodeIdx + 1) (by omega) right hright
                        have hrightCovered := hleftCovered.of_resolveDeferredTreeNode table lay tree
                          level (2 * nodeIdx + 1) (by omega) right hright
                        exact evalDist_map_resolveDeferredPositionValue_then_finalize
                          (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
                          coordinates right.toDeferredContext table hrightValid hrightCovered
                _ = evalDist (projectDeferredState <$>
                    finalizeResolvedCoordinates coordinates left.toDeferredContext table) :=
                  evalDist_map_resolveDeferredTreeNode_then_finalize table lay tree coordinates
                    level (2 * nodeIdx + 1) (by omega) left.toDeferredContext hleftValid
                      hleftCovered
        _ = evalDist (projectDeferredState <$>
            finalizeResolvedCoordinates coordinates context table) :=
          evalDist_map_resolveDeferredTreeNode_then_finalize table lay tree coordinates
            level (2 * nodeIdx) (by omega) context hvalid hcovered

set_option maxRecDepth 100000 in
theorem evalDist_map_resolveDeferredPosition_then_finalize
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (coordinates : List Coordinate) (context : DeferredContext)
    (hvalid : context.Valid) (hcovered : PendingCovered coordinates context) :
    evalDist (do
        let resolved ← resolveDeferredPosition table position context
        match resolved with
        | none => (pure none : ProbComp
            (Option (LazyRevealProbe.State Coordinate)))
        | some resolved => projectDeferredState <$>
            finalizeResolvedCoordinates coordinates resolved.toDeferredContext table) =
      evalDist (projectDeferredState <$>
        finalizeResolvedCoordinates coordinates context table) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact evalDist_map_resolveDeferredChainPrefix_then_finalize table lay tree leafIdx chainIdx
        coordinates context hvalid hcovered (step.val + 1) (by have := step.isLt; omega)
  | leaf lay tree leafIdx =>
      exact evalDist_map_resolveDeferredOtsLeaf_then_finalize table lay tree leafIdx coordinates
        context hvalid hcovered
  | node lay tree level nodeIdx =>
      exact evalDist_map_resolveDeferredTreeNode_then_finalize table lay tree coordinates
        (level.val + 1) nodeIdx (by have := level.isLt; omega) context hvalid hcovered
  | ftsLeaf index tree leafIdx =>
      exact evalDist_map_resolveDeferredPositionValue_then_finalize
        (.ftsLeaf index tree leafIdx) coordinates context table hvalid hcovered
  | ftsNode index tree level nodeIdx =>
      exact evalDist_map_resolveDeferredPositionValue_then_finalize
        (.ftsNode index tree level nodeIdx) coordinates context table hvalid hcovered
  | ftsRoots index =>
      exact evalDist_map_resolveDeferredPositionValue_then_finalize
        (.ftsRoots index) coordinates context table hvalid hcovered

def DeferredCompletion (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (completion : Coordinate → HashOutput) : Prop :=
  (∀ coordinate output, context.state.values coordinate = some output →
      completion coordinate = output) ∧
    (∀ position output, context.values position = some output →
      completion (.position position) = output) ∧
    (∀ coordinate candidate, (coordinate, candidate) ∈ context.state.pending →
      truncateHash (completion coordinate) ≠ candidate) ∧
    ∀ index, completion index.coordinate = table index

def DeferredContext.CoreEq (left right : DeferredContext) : Prop :=
  left.state.pending = right.state.pending ∧
    left.state.values = right.state.values ∧
    left.values = right.values

theorem DeferredContext.CoreEq.symm {left right : DeferredContext}
    (heq : left.CoreEq right) : right.CoreEq left :=
  ⟨heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩

theorem DeferredContext.CoreEq.positionValue_eq {left right : DeferredContext}
    (heq : left.CoreEq right) : left.positionValue = right.positionValue := by
  funext position
  unfold DeferredContext.positionValue
  rw [heq.2.1, heq.2.2]

theorem DeferredContext.CoreEq.hitAt_iff {left right : DeferredContext}
    (heq : left.CoreEq right) (coordinate : Coordinate) (output : HashOutput) :
    left.state.hitAt coordinate output ↔ right.state.hitAt coordinate output := by
  unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt
  rw [heq.1]

theorem DeferredContext.Valid.of_coreEq {left right : DeferredContext}
    (hvalid : left.Valid) (heq : left.CoreEq right) : right.Valid := by
  constructor
  · intro position output hvalue
    rw [← heq.2.2]
    apply hvalid.1 position output
    rw [heq.2.1]
    exact hvalue
  · intro coordinate output hvalue
    rw [← heq.hitAt_iff coordinate output]
    apply hvalid.2 coordinate output
    rw [heq.2.1]
    exact hvalue

theorem StartTableAgrees.of_coreEq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hagrees : StartTableAgrees left.state table) (heq : left.CoreEq right) :
    StartTableAgrees right.state table := by
  intro index output hvalue
  apply hagrees index output
  rw [heq.2.1]
  exact hvalue

theorem StartTableAgrees.of_state_values_eq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (hagrees : StartTableAgrees left.state table)
    (hvalues : right.state.values = left.state.values) :
    StartTableAgrees right.state table := by
  intro index output hvalue
  apply hagrees index output
  rw [← hvalues]
  exact hvalue

theorem DeferredCompletion.of_coreEq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    {completion : Coordinate → HashOutput} (heq : left.CoreEq right)
    (hcompletion : DeferredCompletion table left completion) :
    DeferredCompletion table right completion := by
  refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    apply hcompletion.1 coordinate output
    rw [heq.2.1]
    exact hvalue
  · intro position output hvalue
    apply hcompletion.2.1 position output
    rw [heq.2.2]
    exact hvalue
  · intro coordinate candidate hmember
    apply hcompletion.2.2.1 coordinate candidate
    rw [heq.1]
    exact hmember

theorem DeferredCompletion.of_addPending
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (coordinate : Coordinate)
    (candidate : Digest)
    (hcompletion : DeferredCompletion table
      { context with state := context.state.addPending coordinate candidate } completion) :
    DeferredCompletion table context completion := by
  refine ⟨hcompletion.1, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
  intro other otherCandidate hmember
  apply hcompletion.2.2.1 other otherCandidate
  simp only [LazyRevealProbe.State.addPending, Finset.mem_insert]
  exact Or.inr hmember

theorem DeferredCompletion.eq_positionValue
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion)
    (position : Position) (output : HashOutput)
    (hvalue : context.positionValue position = some output) :
    completion (.position position) = output := by
  unfold DeferredContext.positionValue at hvalue
  cases hstate : context.state.values (.position position) with
  | some cached =>
      have hcached : cached = output := by simpa [hstate] using hvalue
      exact (hcompletion.1 (.position position) cached hstate).trans hcached
  | none =>
      exact hcompletion.2.1 position output (by simpa [hstate] using hvalue)

def materializeResolvedPosition (context : DeferredContext) (position : Position)
    (result : DeferredResolution) : DeferredContext :=
  { state := context.state.materialize (.position position) result.output
    values := result.values }

theorem materializeResolvedPosition_positionValue_eq
    (context : DeferredContext) (position : Position) (result : DeferredResolution)
    (hstateValues : result.state.values = context.state.values)
    (hresolved : result.toDeferredContext.positionValue position = some result.output) :
    (materializeResolvedPosition context position result).positionValue =
      result.toDeferredContext.positionValue := by
  funext other
  by_cases heq : other = position
  · subst other
    rw [hresolved]
    simp [materializeResolvedPosition, DeferredContext.positionValue,
      LazyRevealProbe.State.materialize]
  · unfold DeferredContext.positionValue
    rw [hstateValues]
    simp [materializeResolvedPosition, LazyRevealProbe.State.materialize,
      Function.update_of_ne,
      show Coordinate.position other ≠ Coordinate.position position by simpa using heq]

theorem DeferredContext.ValuesConsistent.materializeResolvedPosition_of
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    (materializeResolvedPosition context position result).ValuesConsistent := by
  have hresultConsistent := hconsistent.of_resolveDeferredReveal table position result hresult
  have hstateValues := resolveDeferredReveal_preserves_state_values table position context result
    hresult
  intro other output hvalue
  by_cases heq : other = position
  · subst other
    have hsame : output = result.output := by
      simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize] using hvalue.symm
    rw [hsame]
    change result.values position = some result.output
    have hresolved := resolveDeferredReveal_resolves table position context result hresult
    unfold DeferredContext.positionValue at hresolved
    cases hstate : result.state.values (.position position) with
    | none => simpa [hstate] using hresolved
    | some cached =>
        have hprivate := hresultConsistent position cached hstate
        have hcached : cached = result.output := by simpa [hstate] using hresolved
        simpa [hcached] using hprivate
  · apply hresultConsistent other output
    rw [hstateValues]
    simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize,
      Function.update_of_ne,
      show Coordinate.position other ≠ Coordinate.position position by simpa using heq]
      using hvalue

theorem DeferredCompletion.of_materializeResolvedPosition
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput} (position : Position)
    (result : DeferredResolution)
    (hstateValues : result.state.values = context.state.values)
    (hpending : result.state.pending ⊆
      context.state.pendingAway (.position position))
    (hresolved : result.toDeferredContext.positionValue position = some result.output)
    (hcompletion : DeferredCompletion table
      (materializeResolvedPosition context position result) completion) :
    DeferredCompletion table result.toDeferredContext completion := by
  refine ⟨?_, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    rw [hstateValues] at hvalue
    by_cases heq : coordinate = .position position
    · subst coordinate
      have hresultValue : result.state.values (.position position) = some output := by
        rw [hstateValues]
        exact hvalue
      unfold DeferredContext.positionValue at hresolved
      rw [hresultValue] at hresolved
      have hsame : output = result.output := Option.some.inj hresolved
      apply hcompletion.1 (.position position) output
      simp [materializeResolvedPosition, LazyRevealProbe.State.materialize, hsame]
    · apply hcompletion.1 coordinate output
      simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize,
        Function.update_of_ne heq] using hvalue
  · intro coordinate candidate hmember
    apply hcompletion.2.2.1 coordinate candidate
    have haway := hpending hmember
    simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize] using haway

theorem DeferredCompletion.of_resolveDeferredPositionValue_of_valuesConsistent
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent) (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context))
    (hcompletion : DeferredCompletion table result.toDeferredContext completion) :
    DeferredCompletion table context completion := by
  have hstateValues := resolveDeferredPositionValue_preserves_state_values
    position context result hresult
  have hresolved := resolveDeferredPositionValue_resolves position context result hresult
  have hnotHit := resolveDeferredPositionValue_not_hit position context result hresult
  have hpending := resolveDeferredPositionValue_pending position context result hresult
  refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    apply hcompletion.1 coordinate output
    rw [hstateValues]
    exact hvalue
  · intro other output hvalue
    have hknown : context.positionValue other = some output := by
      unfold DeferredContext.positionValue
      cases hstate : context.state.values (.position other) with
      | some cached =>
          have hsame := hconsistent other cached hstate
          have : cached = output := by
            rw [hsame] at hvalue
            exact Option.some.inj hvalue
          simp [this]
      | none => simp [hvalue]
    exact hcompletion.eq_positionValue other output
      (resolveDeferredPositionValue_preserves_positionValue position other context result
        output hknown hresult)
  · intro coordinate candidate hmember
    by_cases heq : coordinate = .position position
    · subst coordinate
      have hcompletionValue := hcompletion.eq_positionValue position result.output hresolved
      intro hequal
      apply hnotHit
      unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt
      rw [hcompletionValue] at hequal
      simpa [hequal] using hmember
    · apply hcompletion.2.2.1 coordinate candidate
      rw [hpending]
      simpa [LazyRevealProbe.State.pendingAway, heq] using hmember

theorem DeferredCompletion.of_resolveDeferredPositionValue
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hvalid : context.Valid) (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context))
    (hcompletion : DeferredCompletion table result.toDeferredContext completion) :
    DeferredCompletion table context completion :=
  hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent hvalid.valuesConsistent
    position result hresult

theorem DeferredCompletion.of_resolveDeferredChainStart
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hagrees : StartTableAgrees context.state table) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result)
    (hcompletion : DeferredCompletion table result.toDeferredContext completion) :
    DeferredCompletion table context completion := by
  unfold resolveDeferredChainStart at hresult
  cases hstate : context.state.values index.coordinate with
  | some cached =>
      have hcached := hagrees index cached hstate
      subst cached
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        refine ⟨hcompletion.1, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
        intro coordinate candidate hmember
        by_cases heq : coordinate = index.coordinate
        · subst coordinate
          intro hequal
          apply hhit
          unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt
          rw [hcompletion.2.2.2 index] at hequal
          simpa [hequal] using hmember
        · apply hcompletion.2.2.1 coordinate candidate
          simpa [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway,
            heq] using hmember
  | none =>
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        refine ⟨hcompletion.1, hcompletion.2.1, ?_, hcompletion.2.2.2⟩
        intro coordinate candidate hmember
        by_cases heq : coordinate = index.coordinate
        · subst coordinate
          intro hequal
          apply hhit
          unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt
          rw [hcompletion.2.2.2 index] at hequal
          simpa [hequal] using hmember
        · apply hcompletion.2.2.1 coordinate candidate
          simpa [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway,
            heq] using hmember

theorem DeferredCompletion.of_resolveDeferredChainPrefix
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps result,
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      DeferredCompletion table result.toDeferredContext completion →
      DeferredCompletion table context completion
  | 0, hsteps, result, hresult, hcompletion => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      exact hcompletion.of_resolveDeferredChainStart hstarts ⟨lay, tree, leafIdx, chainIdx⟩
        result hresult.symm
  | steps + 1, hsteps, result, hresult, hcompletion => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hpreviousConsistent := hconsistent.of_resolveDeferredChainPrefix table lay tree
            leafIdx chainIdx steps (by omega) previous hprevious
          have hbeforeLast := hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent
            hpreviousConsistent (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) result
              (by simpa using hrest)
          exact hbeforeLast.of_resolveDeferredChainPrefix hconsistent hstarts lay tree leafIdx
            chainIdx steps (by omega) previous hprevious

theorem DeferredCompletion.of_resolveDeferredChains
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) : ∀ chains result,
      some result ∈ support
        (resolveDeferredChains table lay tree leafIdx chains context) →
      DeferredCompletion table result completion →
      DeferredCompletion table context completion
  | [], result, hresult, hcompletion => by
      simp [resolveDeferredChains] at hresult
      subst result
      exact hcompletion
  | chainIdx :: remaining, result, hresult, hcompletion => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          have hresolvedConsistent := hconsistent.of_resolveDeferredChainPrefix table lay tree
            leafIdx chainIdx (chainLength - 1) (by omega) resolved hresolved
          have hstateValues := resolveDeferredChainPrefix_preserves_state_values table lay tree
            leafIdx chainIdx (chainLength - 1) (by omega) context resolved hresolved
          have hresolvedStarts := hstarts.of_state_values_eq hstateValues
          have hbeforeTail := hcompletion.of_resolveDeferredChains hresolvedConsistent
            hresolvedStarts lay tree leafIdx remaining result (by simpa using hrest)
          exact hbeforeTail.of_resolveDeferredChainPrefix hconsistent hstarts lay tree leafIdx
            chainIdx (chainLength - 1) (by omega) resolved hresolved

theorem DeferredCompletion.of_resolveDeferredOtsLeaf
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context))
    (hcompletion : DeferredCompletion table result.toDeferredContext completion) :
    DeferredCompletion table context completion := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      have hchainsConsistent := hconsistent.of_resolveDeferredChains table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
      have hbeforeLeaf := hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent
        hchainsConsistent (.leaf lay tree leafIdx) result (by simpa using hrest)
      exact hbeforeLeaf.of_resolveDeferredChains hconsistent hstarts lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains

theorem DeferredCompletion.of_resolveDeferredTreeNode
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel result,
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      DeferredCompletion table result.toDeferredContext completion →
      DeferredCompletion table context completion
  | 0, nodeIdx, hlevel, result, hresult, hcompletion =>
      hcompletion.of_resolveDeferredOtsLeaf hconsistent hstarts lay tree (leafOfNat nodeIdx)
        result hresult
  | level + 1, nodeIdx, hlevel, result, hresult, hcompletion => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hleftConsistent := hconsistent.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) left hleft
              have hleftState := resolveDeferredTreeNode_preserves_state_values table lay tree level
                (2 * nodeIdx) (by omega) context left hleft
              have hleftStarts := hstarts.of_state_values_eq hleftState
              have hrightConsistent := hleftConsistent.of_resolveDeferredTreeNode table lay tree
                level (2 * nodeIdx + 1) (by omega) right hright
              have hrightState := resolveDeferredTreeNode_preserves_state_values table lay tree
                level (2 * nodeIdx + 1) (by omega) left.toDeferredContext right hright
              have hrightStarts := hleftStarts.of_state_values_eq hrightState
              have hbeforeNode :=
                hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent
                  hrightConsistent (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx))
                    result (by simpa using hafterRight)
              have hbeforeRight := hbeforeNode.of_resolveDeferredTreeNode hleftConsistent
                hleftStarts lay tree level (2 * nodeIdx + 1) (by omega) right hright
              exact hbeforeRight.of_resolveDeferredTreeNode hconsistent hstarts lay tree level
                (2 * nodeIdx) (by omega) left hleft

theorem DeferredCompletion.of_resolveDeferredPosition
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredPosition table position context))
    (hcompletion : DeferredCompletion table result.toDeferredContext completion) :
    DeferredCompletion table context completion := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact hcompletion.of_resolveDeferredChainPrefix hconsistent hstarts lay tree leafIdx chainIdx
        (step.val + 1) (by have := step.isLt; omega) result hresult
  | leaf lay tree leafIdx =>
      exact hcompletion.of_resolveDeferredOtsLeaf hconsistent hstarts lay tree leafIdx result
        hresult
  | node lay tree level nodeIdx =>
      exact hcompletion.of_resolveDeferredTreeNode hconsistent hstarts lay tree
        (level.val + 1) nodeIdx (by have := level.isLt; omega) result hresult
  | ftsLeaf index tree leafIdx =>
      exact hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent hconsistent
        (.ftsLeaf index tree leafIdx) result hresult
  | ftsNode index tree level nodeIdx =>
      exact hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent hconsistent
        (.ftsNode index tree level nodeIdx) result hresult
  | ftsRoots index =>
      exact hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent hconsistent
        (.ftsRoots index) result hresult

theorem DeferredCompletion.of_resolveDeferredReveal
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) (position : Position)
    (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredReveal table position context))
    (hcompletion : DeferredCompletion table result.toDeferredContext completion) :
    DeferredCompletion table context completion := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · apply hcompletion.of_resolveDeferredPosition hconsistent hstarts position result
    simpa [resolveDeferredReveal, hresolvable] using hresult
  · apply hcompletion.of_resolveDeferredPositionValue_of_valuesConsistent hconsistent
      position result
    simpa [resolveDeferredReveal, hresolvable] using hresult

theorem resolveDeferredChainStart_positionValue_eq
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    result.toDeferredContext.positionValue = context.positionValue := by
  unfold resolveDeferredChainStart at hresult
  cases hstate : context.state.values index.coordinate with
  | some output =>
      by_cases hhit : context.state.hitAt index.coordinate output
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        rfl
  | none =>
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        rfl

theorem resolveDeferredChainStart_state_values_eq
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    result.state.values = context.state.values := by
  unfold resolveDeferredChainStart at hresult
  cases hstate : context.state.values index.coordinate with
  | some output =>
      by_cases hhit : context.state.hitAt index.coordinate output
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        rfl
  | none =>
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        rfl

theorem resolveDeferredChainStart_deferred_values_eq
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    result.values = context.values := by
  unfold resolveDeferredChainStart at hresult
  cases hstate : context.state.values index.coordinate with
  | some output =>
      by_cases hhit : context.state.hitAt index.coordinate output
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        rfl
  | none =>
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        rfl

theorem resolveDeferredChainStart_pending_eq
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    result.state.pending = context.state.pendingAway index.coordinate := by
  unfold resolveDeferredChainStart at hresult
  cases hstate : context.state.values index.coordinate with
  | some output =>
      by_cases hhit : context.state.hitAt index.coordinate output
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        rfl

  | none =>
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hstate, hhit] at hresult
      · simp [hstate, hhit] at hresult
        subst result
        rfl

def materializeResolvedChainStart (context : DeferredContext) (index : OtsSecretIndex)
    (result : DeferredResolution) : DeferredContext :=
  { state := context.state.materialize index.coordinate result.output
    values := result.values }

theorem materializeResolvedChainStart_positionValue_eq
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    (materializeResolvedChainStart context index result).positionValue =
      context.positionValue := by
  funext position
  unfold DeferredContext.positionValue
  change (match (context.state.materialize index.coordinate result.output).values
      (.position position) with
    | some output => some output
    | none => result.values position) = _
  rw [resolveDeferredChainStart_deferred_values_eq table index context result hresult]
  simp [LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate]

theorem DeferredContext.ValuesConsistent.materializeResolvedChainStart_of
    {context : DeferredContext} (hconsistent : context.ValuesConsistent)
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    (materializeResolvedChainStart context index result).ValuesConsistent := by
  intro position output hvalue
  change result.values position = some output
  rw [resolveDeferredChainStart_deferred_values_eq table index context result hresult]
  apply hconsistent position output
  simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize,
    OtsSecretIndex.coordinate] using hvalue

theorem DeferredCompletion.of_materializeResolvedChainStart
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hagrees : StartTableAgrees context.state table) (index : OtsSecretIndex)
    (hcompletable : ∃ baseCompletion, DeferredCompletion table context baseCompletion)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result)
    (hcompletion : DeferredCompletion table
      (materializeResolvedChainStart context index result) completion) :
    DeferredCompletion table context completion := by
  have houtput := resolveDeferredChainStart_output_of_agrees table index context result hagrees
    hresult
  have hdeferred := resolveDeferredChainStart_deferred_values_eq table index context result
    hresult
  refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    by_cases heq : coordinate = index.coordinate
    · subst coordinate
      have htable := hagrees index output hvalue
      apply hcompletion.1 index.coordinate output
      simp [materializeResolvedChainStart, LazyRevealProbe.State.materialize, houtput,
        htable]
    · apply hcompletion.1 coordinate output
      simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize,
        Function.update_of_ne heq] using hvalue
  · intro position output hvalue
    apply hcompletion.2.1 position output
    simpa [materializeResolvedChainStart, hdeferred] using hvalue
  · intro coordinate candidate hmember
    by_cases heq : coordinate = index.coordinate
    · subst coordinate
      obtain ⟨baseCompletion, hbaseCompletion⟩ := hcompletable
      have havoid := hbaseCompletion.2.2.1 index.coordinate candidate hmember
      rw [hbaseCompletion.2.2.2 index] at havoid
      rw [hcompletion.2.2.2 index]
      exact havoid
    · apply hcompletion.2.2.1 coordinate candidate
      have haway : (coordinate, candidate) ∈ context.state.pendingAway index.coordinate :=
        Finset.mem_filter.2 ⟨hmember, heq⟩
      simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize] using haway

theorem resolveDeferredChainStart_not_hit
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hagrees : StartTableAgrees context.state table) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    ¬context.state.hitAt index.coordinate (table index) := by
  unfold resolveDeferredChainStart at hresult
  cases hvalue : context.state.values index.coordinate with
  | none =>
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hvalue, hhit] at hresult
      · exact hhit
  | some output =>
      have houtput := hagrees index output hvalue
      subst output
      by_cases hhit : context.state.hitAt index.coordinate (table index)
      · simp [hvalue, hhit] at hresult
      · exact hhit

theorem DeferredCompletion.of_materializeResolvedChainStart'
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hagrees : StartTableAgrees context.state table) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result)
    (hcompletion : DeferredCompletion table
      (materializeResolvedChainStart context index result) completion) :
    DeferredCompletion table context completion := by
  have houtput := resolveDeferredChainStart_output_of_agrees table index context result hagrees
    hresult
  have hdeferred := resolveDeferredChainStart_deferred_values_eq table index context result
    hresult
  have hnotHit := resolveDeferredChainStart_not_hit hagrees index result hresult
  refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    by_cases heq : coordinate = index.coordinate
    · subst coordinate
      have htable := hagrees index output hvalue
      apply hcompletion.1 index.coordinate output
      simp [materializeResolvedChainStart, LazyRevealProbe.State.materialize, houtput,
        htable]
    · apply hcompletion.1 coordinate output
      simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize,
        Function.update_of_ne heq] using hvalue
  · intro position output hvalue
    apply hcompletion.2.1 position output
    simpa [materializeResolvedChainStart, hdeferred] using hvalue
  · intro coordinate candidate hmember
    by_cases heq : coordinate = index.coordinate
    · subst coordinate
      intro hequal
      apply hnotHit
      unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt
      rw [hcompletion.2.2.2 index] at hequal
      simpa [hequal] using hmember
    · apply hcompletion.2.2.1 coordinate candidate
      have haway : (coordinate, candidate) ∈ context.state.pendingAway index.coordinate :=
        Finset.mem_filter.2 ⟨hmember, heq⟩
      simpa [materializeResolvedChainStart, LazyRevealProbe.State.materialize] using haway

set_option maxRecDepth 100000 in
theorem deferredCompletable_of_mem_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult alpha)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation))
    (hfinal : ∃ completion, DeferredCompletion table result.context completion) :
    ∃ completion, DeferredCompletion table context completion := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact hfinal
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hconsistent hstarts hrest
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hconsistent hstarts hrest
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          have hcurrent := ih () { context with state := context.state.ensure coordinate } fuel
            (hconsistent.ensure coordinate) (hstarts.ensure coordinate) hresult
          obtain ⟨completion, hcompletion⟩ := hcurrent
          exact ⟨completion, hcompletion.of_coreEq ⟨rfl, rfl, rfl⟩⟩
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining hconsistent hstarts
                  (by simpa [hrevealed] using hresult)
              · have hcurrent := ih ()
                    { context with state := context.state.addPending coordinate candidate }
                    remaining (hconsistent.addPending coordinate candidate)
                    (hstarts.addPending coordinate candidate)
                    (by simpa [hrevealed] using hresult)
                obtain ⟨completion, hcompletion⟩ := hcurrent
                exact ⟨completion, hcompletion.of_addPending coordinate candidate⟩
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hconsistent hstarts hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          have hcurrent := ih () { context with state := context.state.publish coordinate } fuel
            (hconsistent.publish coordinate) (hstarts.publish coordinate) hresult
          obtain ⟨completion, hcompletion⟩ := hcurrent
          exact ⟨completion, hcompletion.of_coreEq ⟨rfl, rfl, rfl⟩⟩
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
              obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  have hresolvedEq : resolveDeferredChainStart table index context =
                      some resolved := by simpa [index] using hresolved.symm
                  have hmaterializedConsistent :=
                    hconsistent.materializeResolvedChainStart_of table index resolved hresolvedEq
                  have houtput := resolveDeferredChainStart_output_of_agrees table index context
                    resolved hstarts hresolvedEq
                  have hmaterializedStarts : StartTableAgrees
                      (context.state.materialize index.coordinate resolved.output) table := by
                    rw [houtput]
                    exact hstarts.materialize_start index
                  have hcurrent := ih resolved.output
                    (materializeResolvedChainStart context index resolved) fuel
                    hmaterializedConsistent (by
                      simpa [materializeResolvedChainStart] using hmaterializedStarts)
                    (by simpa [index, OtsSecretIndex.coordinate, materializeResolvedChainStart]
                      using hrest)
                  obtain ⟨completion, hcompletion⟩ := hcurrent
                  exact ⟨completion,
                    hcompletion.of_materializeResolvedChainStart' hstarts index resolved hresolvedEq⟩
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  have hmaterializedConsistent :=
                    hconsistent.materializeResolvedPosition_of table position resolved hresolved
                  have hmaterializedStarts : StartTableAgrees
                      (context.state.materialize (.position position) resolved.output) table :=
                    hstarts.materialize_position position resolved.output
                  have hcurrent := ih resolved.output
                    (materializeResolvedPosition context position resolved) fuel
                    hmaterializedConsistent (by
                      simpa [materializeResolvedPosition] using hmaterializedStarts)
                    (by simpa [materializeResolvedPosition] using hrest)
                  obtain ⟨completion, hcompletion⟩ := hcurrent
                  have hstateValues := resolveDeferredReveal_preserves_state_values table position
                    context resolved hresolved
                  have hpending := resolveDeferredReveal_pendingAway_subset table position context
                    resolved hresolved
                  have hresolvedValue := resolveDeferredReveal_resolves table position context
                    resolved hresolved
                  have hbeforeMaterialize := hcompletion.of_materializeResolvedPosition position
                    resolved hstateValues hpending hresolvedValue
                  exact ⟨completion, hbeforeMaterialize.of_resolveDeferredReveal
                    hconsistent hstarts position resolved hresolved⟩

set_option maxRecDepth 100000 in
theorem resolvedCore_of_mem_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult alpha)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation)) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact ⟨rfl, hconsistent, hstarts⟩
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hconsistent hstarts hrest
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hconsistent hstarts hrest
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel
            (hconsistent.ensure coordinate) (hstarts.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining hconsistent hstarts
                  (by simpa [hrevealed] using hresult)
              · exact ih () { context with state := context.state.addPending coordinate candidate }
                  remaining (hconsistent.addPending coordinate candidate)
                  (hstarts.addPending coordinate candidate)
                  (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hconsistent hstarts hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel
            (hconsistent.publish coordinate) (hstarts.publish coordinate) hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
              obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  have hresolvedEq : resolveDeferredChainStart table index context =
                      some resolved := by simpa [index] using hresolved.symm
                  have hmaterializedConsistent :=
                    hconsistent.materializeResolvedChainStart_of table index resolved hresolvedEq
                  have houtput := resolveDeferredChainStart_output_of_agrees table index context
                    resolved hstarts hresolvedEq
                  have hmaterializedStarts : StartTableAgrees
                      (context.state.materialize index.coordinate resolved.output) table := by
                    rw [houtput]
                    exact hstarts.materialize_start index
                  exact ih resolved.output (materializeResolvedChainStart context index resolved)
                    fuel hmaterializedConsistent (by
                      simpa [materializeResolvedChainStart] using hmaterializedStarts)
                    (by simpa [index, OtsSecretIndex.coordinate, materializeResolvedChainStart]
                      using hrest)
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  have hmaterializedConsistent :=
                    hconsistent.materializeResolvedPosition_of table position resolved hresolved
                  have hmaterializedStarts : StartTableAgrees
                      (context.state.materialize (.position position) resolved.output) table :=
                    hstarts.materialize_position position resolved.output
                  exact ih resolved.output (materializeResolvedPosition context position resolved)
                    fuel hmaterializedConsistent (by
                      simpa [materializeResolvedPosition] using hmaterializedStarts)
                    (by simpa [materializeResolvedPosition] using hrest)

def ChronologicalCacheAgrees (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (cache : QueryCache HashSpec) : Prop :=
  ∀ completion, DeferredCompletion table context completion →
    ∀ position, IsOtsPosition position →
      ResolveInputAgrees position context
        (tableInput parameter completion (.position position)) cache

theorem chronologicalCacheAgrees_empty (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) :
    ChronologicalCacheAgrees parameter table
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }
      (∅ : QueryCache HashSpec) := by
  intro completion hcompletion position hots
  simp [ResolveInputAgrees, DeferredContext.positionValue,
    LazyRevealProbe.State.empty, emptyDeferredStructuralValues]

theorem ChronologicalCacheAgrees.of_resolveDeferredChainStart
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hcache : ChronologicalCacheAgrees parameter table context cache)
    (hagrees : StartTableAgrees context.state table) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    ChronologicalCacheAgrees parameter table result.toDeferredContext cache := by
  intro completion hcompletion position hots
  have horiginal := hcompletion.of_resolveDeferredChainStart hagrees index result hresult
  have hknown := hcache completion horiginal position hots
  have hvalues := congrFun
    (resolveDeferredChainStart_positionValue_eq table index context result hresult) position
  unfold ResolveInputAgrees at hknown ⊢
  rw [hvalues]
  exact hknown

theorem ChronologicalCacheAgrees.of_resolveDeferredPositionValue
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hagrees : ChronologicalCacheAgrees parameter table context cache)
    (hvalid : context.Valid) (position : Position) (input : HashInput)
    (hcanonical : ∀ completion, DeferredCompletion table context completion →
      input = tableInput parameter completion (.position position))
    (result : DeferredResolution) (output : HashOutput)
    (finalCache : QueryCache HashSpec)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context))
    (hquery : ResolveQueryRel input cache (some result) (output, finalCache)) :
    ChronologicalCacheAgrees parameter table result.toDeferredContext finalCache := by
  rcases hquery with ⟨houtput, rfl⟩
  subst output
  intro completion hcompletion other hots
  have hcompletionOriginal := hcompletion.of_resolveDeferredPositionValue
    hvalid position result hresult
  have hinput := hcanonical completion hcompletionOriginal
  by_cases heq : other = position
  · subst other
    have hresolved := resolveDeferredPositionValue_resolves position context result hresult
    unfold ResolveInputAgrees
    rw [hresolved, ← hinput]
    simp
  · have hknown := hagrees completion hcompletionOriginal other hots
    have hpreserved : result.toDeferredContext.positionValue other =
        context.positionValue other := by
      unfold DeferredContext.positionValue
      rw [resolveDeferredPositionValue_preserves_state_values position context result hresult,
        resolveDeferredPositionValue_preserves_other position other context result heq hresult]
    have hinputNe : tableInput parameter completion (.position other) ≠ input := by
      intro hequal
      have hdomains := (tweakableHashInput_injective parameter
        position.domain_inRange other.domain_inRange (by
          simpa [tableInput] using hinput.symm.trans hequal.symm)).1
      exact heq (Position.domain_injective hdomains).symm
    unfold ResolveInputAgrees at hknown ⊢
    rw [hpreserved]
    cases hvalue : context.positionValue other with
    | none =>
        rw [hvalue] at hknown
        simp only at hknown ⊢
        rw [QueryCache.cacheQuery_of_ne cache result.output hinputNe]
        exact hknown
    | some output =>
        rw [hvalue] at hknown
        simp only at hknown ⊢
        rw [QueryCache.cacheQuery_of_ne cache result.output hinputNe]
        exact hknown

def DeferredCompletable (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : Prop :=
  ∃ completion, DeferredCompletion table context completion

theorem not_deferredCompletable_of_mem_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult alpha)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation))
    (hdoomed : ¬DeferredCompletable table context) :
    ¬DeferredCompletable table result.context := by
  intro hfinal
  exact hdoomed (deferredCompletable_of_mem_runResolvedFromTable computation context fuel table
    result hconsistent hstarts hresult hfinal)

theorem deferredCompletable_iff_of_coreEq
    {table : OtsSecretIndex → HashOutput} {left right : DeferredContext}
    (heq : left.CoreEq right) :
    DeferredCompletable table left ↔ DeferredCompletable table right := by
  constructor
  · rintro ⟨completion, hcompletion⟩
    exact ⟨completion, hcompletion.of_coreEq heq⟩
  · rintro ⟨completion, hcompletion⟩
    exact ⟨completion, hcompletion.of_coreEq heq.symm⟩

theorem DeferredCompletable.materializeResolvedChainStart
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context)
    (hagrees : StartTableAgrees context.state table) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    DeferredCompletable table (materializeResolvedChainStart context index result) := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have houtput := resolveDeferredChainStart_output_of_agrees table index context result hagrees
    hresult
  have hdeferred := resolveDeferredChainStart_deferred_values_eq table index context result
    hresult
  refine ⟨completion, ?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    change (context.state.materialize index.coordinate result.output).values coordinate =
      some output at hvalue
    by_cases heq : coordinate = index.coordinate
    · subst coordinate
      have hsame : output = result.output := by
        simpa [LazyRevealProbe.State.materialize] using hvalue.symm
      rw [hsame, houtput, hcompletion.2.2.2 index]
    · apply hcompletion.1 coordinate output
      simpa [LazyRevealProbe.State.materialize,
        Function.update_of_ne heq] using hvalue
  · intro position output hvalue
    change result.values position = some output at hvalue
    apply hcompletion.2.1 position output
    simpa [hdeferred] using hvalue
  · intro coordinate candidate hmember
    apply hcompletion.2.2.1 coordinate candidate
    change (coordinate, candidate) ∈ context.state.pendingAway index.coordinate at hmember
    have haway : (coordinate, candidate) ∈ context.state.pendingAway index.coordinate := by
      exact hmember
    exact (Finset.mem_filter.1 haway).1

theorem DeferredCompletable.not_hitAt_chainStart
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (index : OtsSecretIndex) :
    ¬context.state.hitAt index.coordinate (table index) := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  intro hhit
  unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt at hhit
  obtain ⟨entry, hentry, heq⟩ := Finset.mem_image.1 hhit
  have hparts := Finset.mem_filter.1 hentry
  have havoid := hcompletion.2.2.1 entry.1 entry.2 hparts.1
  have hcoordinate : entry.1 = index.coordinate := hparts.2
  rw [hcoordinate, hcompletion.2.2.2 index, heq] at havoid
  exact havoid rfl

theorem DeferredCompletable.of_resolveDeferredChainStart
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    DeferredCompletable table result.toDeferredContext := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  refine ⟨completion, ?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    apply hcompletion.1 coordinate output
    rw [← resolveDeferredChainStart_state_values_eq table index context result hresult]
    exact hvalue
  · intro position output hvalue
    apply hcompletion.2.1 position output
    rw [← resolveDeferredChainStart_deferred_values_eq table index context result hresult]
    exact hvalue
  · intro coordinate candidate hmember
    have hpending := resolveDeferredChainStart_pending_eq table index context result hresult
    have hmemberAway : (coordinate, candidate) ∈
        context.state.pendingAway index.coordinate := by
      rw [← hpending]
      exact hmember
    have hparts : (coordinate, candidate) ∈ context.state.pending ∧
        coordinate ≠ index.coordinate := by
      simpa [LazyRevealProbe.State.pendingAway] using hmemberAway
    apply hcompletion.2.2.1 coordinate candidate
    exact hparts.1

theorem DeferredCompletable.of_resolveDeferredPositionValue
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (hvalid : context.Valid)
    (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    DeferredCompletable table result.toDeferredContext := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  let updated := Function.update completion (.position position) result.output
  have hstateValues := resolveDeferredPositionValue_preserves_state_values
    position context result hresult
  have hpending := resolveDeferredPositionValue_pending position context result hresult
  have hresultValid := hvalid.of_resolveDeferredPositionValue position result hresult
  refine ⟨updated, ?_, ?_, ?_, ?_⟩
  · intro coordinate output hvalue
    by_cases heq : coordinate = .position position
    · subst coordinate
      have hprivate := hresultValid.1 position output hvalue
      have hinstalled := resolveDeferredPositionValue_installs position context result hresult
      have hsame : output = result.output := by
        rw [hinstalled] at hprivate
        exact Option.some.inj hprivate.symm
      simp [updated, hsame]
    · simp [updated, Function.update_of_ne heq]
      apply hcompletion.1 coordinate output
      rw [← hstateValues]
      exact hvalue
  · intro other output hvalue
    by_cases heq : other = position
    · subst other
      have hinstalled := resolveDeferredPositionValue_installs position context result hresult
      have hsame : output = result.output := by
        rw [hinstalled] at hvalue
        exact Option.some.inj hvalue.symm
      simp [updated, hsame]
    · have horiginal := resolveDeferredPositionValue_preserves_other
        position other context result heq hresult
      simp [updated, show Coordinate.position other ≠ Coordinate.position position by
        simpa using heq]
      apply hcompletion.2.1 other output
      rw [← horiginal]
      exact hvalue
  · intro coordinate candidate hmember
    have hmemberAway : (coordinate, candidate) ∈
        context.state.pendingAway (.position position) := by
      rw [← hpending]
      exact hmember
    have hparts : (coordinate, candidate) ∈ context.state.pending ∧
        coordinate ≠ .position position := by
      simpa [LazyRevealProbe.State.pendingAway] using hmemberAway
    have hne := hparts.2
    simpa [updated, Function.update_of_ne hne] using
      hcompletion.2.2.1 coordinate candidate hparts.1
  · intro index
    simpa [updated, show index.coordinate ≠ Coordinate.position position by
      cases index
      simp [OtsSecretIndex.coordinate]] using hcompletion.2.2.2 index

theorem deferredCompletable_empty (table : OtsSecretIndex → HashOutput) :
    DeferredCompletable table
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues } := by
  let completion : Coordinate → HashOutput
    | .chainStart lay tree leafIdx chainIdx => table ⟨lay, tree, leafIdx, chainIdx⟩
    | .position _ => 0
  refine ⟨completion, ?_, ?_, ?_, ?_⟩
  · intro coordinate output hvalue
    simp [LazyRevealProbe.State.empty] at hvalue
  · intro position output hvalue
    simp [emptyDeferredStructuralValues] at hvalue
  · intro coordinate candidate hmember
    simp [LazyRevealProbe.State.empty] at hmember
  · intro index
    cases index
    rfl

theorem DeferredCompletable.of_resolveDeferredChainPrefix
    {table : OtsSecretIndex → HashOutput} {lay : Layer} {tree : TreeIndex}
    {leafIdx : LeafIndex} {chainIdx : ChainIndex} :
    ∀ {steps hsteps context result},
      DeferredCompletable table context → context.Valid →
      some result ∈ support
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context) →
      DeferredCompletable table result.toDeferredContext
  | 0, hsteps, context, result, hcompletable, _hvalid, hresult => by
      simp only [resolveDeferredChainPrefix, support_pure, Set.mem_singleton_iff] at hresult
      exact hcompletable.of_resolveDeferredChainStart
        ⟨lay, tree, leafIdx, chainIdx⟩ result hresult.symm
  | steps + 1, hsteps, context, result, hcompletable, hvalid, hresult => by
      rw [resolveDeferredChainPrefix, mem_support_bind_iff] at hresult
      obtain ⟨previousOption, hprevious, hrest⟩ := hresult
      cases previousOption with
      | none => simp at hrest
      | some previous =>
          have hmiddleCompletable := DeferredCompletable.of_resolveDeferredChainPrefix
            hcompletable hvalid hprevious
          have hmiddleValid := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx
            chainIdx steps (by omega) previous hprevious
          exact hmiddleCompletable.of_resolveDeferredPositionValue hmiddleValid
            (.chain lay tree leafIdx chainIdx ⟨steps, by omega⟩) result (by simpa using hrest)

theorem DeferredCompletable.of_resolveDeferredChains
    {table : OtsSecretIndex → HashOutput} {lay : Layer} {tree : TreeIndex}
    {leafIdx : LeafIndex} :
    ∀ {chains context result},
      DeferredCompletable table context → context.Valid →
      some result ∈ support (resolveDeferredChains table lay tree leafIdx chains context) →
      DeferredCompletable table result
  | [], context, result, hcompletable, _hvalid, hresult => by
      simp [resolveDeferredChains] at hresult
      subst result
      exact hcompletable
  | chainIdx :: remaining, context, result, hcompletable, hvalid, hresult => by
      rw [resolveDeferredChains, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          have hmiddleCompletable := hcompletable.of_resolveDeferredChainPrefix hvalid hresolved
          have hmiddleValid := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx
            chainIdx (chainLength - 1) (by omega) resolved hresolved
          exact hmiddleCompletable.of_resolveDeferredChains hmiddleValid (by simpa using hrest)

theorem DeferredCompletable.of_resolveDeferredOtsLeaf
    {table : OtsSecretIndex → HashOutput} {lay : Layer} {tree : TreeIndex}
    {leafIdx : LeafIndex} {context : DeferredContext} {result : DeferredResolution}
    (hcompletable : DeferredCompletable table context) (hvalid : context.Valid)
    (hresult : some result ∈ support
      (resolveDeferredOtsLeaf table lay tree leafIdx context)) :
    DeferredCompletable table result.toDeferredContext := by
  rw [resolveDeferredOtsLeaf, mem_support_bind_iff] at hresult
  obtain ⟨chainsOption, hchains, hrest⟩ := hresult
  cases chainsOption with
  | none => simp at hrest
  | some chains =>
      have hmiddleCompletable := hcompletable.of_resolveDeferredChains hvalid hchains
      have hmiddleValid := hvalid.of_resolveDeferredChains table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
      exact hmiddleCompletable.of_resolveDeferredPositionValue hmiddleValid
        (.leaf lay tree leafIdx) result (by simpa using hrest)

theorem DeferredCompletable.of_resolveDeferredTreeNode
    {table : OtsSecretIndex → HashOutput} {lay : Layer} {tree : TreeIndex} :
    ∀ {level nodeIdx hlevel context result},
      DeferredCompletable table context → context.Valid →
      some result ∈ support
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context) →
      DeferredCompletable table result.toDeferredContext
  | 0, nodeIdx, hlevel, context, result, hcompletable, hvalid, hresult =>
      hcompletable.of_resolveDeferredOtsLeaf hvalid hresult
  | level + 1, nodeIdx, hlevel, context, result, hcompletable, hvalid, hresult => by
      rw [resolveDeferredTreeNode, mem_support_bind_iff] at hresult
      obtain ⟨leftOption, hleft, hafterLeft⟩ := hresult
      cases leftOption with
      | none => simp at hafterLeft
      | some left =>
          rw [mem_support_bind_iff] at hafterLeft
          obtain ⟨rightOption, hright, hafterRight⟩ := hafterLeft
          cases rightOption with
          | none => simp at hafterRight
          | some right =>
              have hleftCompletable := hcompletable.of_resolveDeferredTreeNode hvalid hleft
              have hleftValid := hvalid.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) left hleft
              have hrightCompletable := hleftCompletable.of_resolveDeferredTreeNode
                hleftValid hright
              have hrightValid := hleftValid.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx + 1) (by omega) right hright
              exact hrightCompletable.of_resolveDeferredPositionValue hrightValid
                (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) result
                (by simpa using hafterRight)

theorem DeferredCompletable.of_resolveDeferredPosition
    {table : OtsSecretIndex → HashOutput} {position : Position}
    {context : DeferredContext} {result : DeferredResolution}
    (hcompletable : DeferredCompletable table context) (hvalid : context.Valid)
    (hresult : some result ∈ support (resolveDeferredPosition table position context)) :
    DeferredCompletable table result.toDeferredContext := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact hcompletable.of_resolveDeferredChainPrefix hvalid hresult
  | leaf lay tree leafIdx => exact hcompletable.of_resolveDeferredOtsLeaf hvalid hresult
  | node lay tree level nodeIdx => exact hcompletable.of_resolveDeferredTreeNode hvalid hresult
  | ftsLeaf index tree leafIdx =>
      exact hcompletable.of_resolveDeferredPositionValue hvalid (.ftsLeaf index tree leafIdx)
        result hresult
  | ftsNode index tree level nodeIdx =>
      exact hcompletable.of_resolveDeferredPositionValue hvalid
        (.ftsNode index tree level nodeIdx) result hresult
  | ftsRoots index =>
      exact hcompletable.of_resolveDeferredPositionValue hvalid (.ftsRoots index) result hresult

def FixedResolvedInput (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (input : HashInput) (output : HashOutput) : Prop :=
  ∃ position : Position,
    IsOtsPosition position ∧
      context.positionValue position = some output ∧
      ∀ completion, DeferredCompletion table context completion →
        input = tableInput parameter completion (.position position)

def ResolvedCachePartition (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (ordinaryCache concreteCache : QueryCache HashSpec) : Prop :=
  (∀ input output, ordinaryCache input = some output →
      concreteCache input = some output) ∧
    ∀ input output, concreteCache input = some output →
      ordinaryCache input = some output ∨
        FixedResolvedInput parameter table context input output

def CompletionOrdinaryInput (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (input : HashInput) : Prop :=
  ∀ completion, DeferredCompletion table context completion →
    ∀ position, IsOtsPosition position →
      input ≠ tableInput parameter completion (.position position)

theorem completionOrdinaryInput_of_stable
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {input : HashInput}
    (hstable : StableOrdinaryInput parameter input) :
    CompletionOrdinaryInput parameter table context input := by
  intro completion hcompletion position hots heq
  have hdecoded : decodePosition? parameter input = some position := by
    rw [heq]
    exact (decodePosition?_eq_some_iff parameter _ position).2
      ⟨tablePayload completion position, rfl⟩
  exact hstable.2 position hdecoded hots

theorem completionOrdinaryInput_of_pending_decodedProbe
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {input : HashInput} {candidate : Probe}
    (hdecode : decodeProbe? parameter input = some candidate)
    (hpending : (candidate.coordinate, candidate.candidate) ∈ context.state.pending) :
    CompletionOrdinaryInput parameter table context input := by
  intro completion hcompletion position hots heq
  have hmatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hdecode
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      have hcanonical :
          (chainInputProbe completion lay tree leafIdx chainIdx step).MatchesInput parameter
            input := by
        rw [heq]
        exact chainInputProbe_matchesInput parameter completion lay tree leafIdx chainIdx step
      have hcandidates := Probe.matchesInput_unique parameter input hmatches hcanonical
      subst candidate
      have havoids := hcompletion.2.2.1
        (chainInputSource lay tree leafIdx chainIdx step)
        (truncateHash (completion (chainInputSource lay tree leafIdx chainIdx step))) (by
          simpa [chainInputProbe] using hpending)
      exact havoids rfl
  | leaf lay tree leafIdx =>
      have hcanonicalDecode : decodeProbe? parameter
          (tableInput parameter completion (.position (.leaf lay tree leafIdx))) =
            some candidate := by
        simpa [heq] using hdecode
      have hcandidates := decodeProbe?_tableInput_leaf_eq parameter completion lay tree leafIdx
        candidate hcanonicalDecode
      subst candidate
      have hzero : 0 < (Position.leaf lay tree leafIdx).children.length := by
        simp [Position.children, numChains]
      have hslot := slotDigest_tableInput_leaf_getElem parameter completion lay tree leafIdx 0
        hzero
      rw [leaf_children_getElem_zero lay tree leafIdx hzero] at hslot
      have havoids := hcompletion.2.2.1
        (.position (.chain lay tree leafIdx
          ⟨0, by norm_num [numChains]⟩ Position.lastChainStep))
        (slotDigest 0
          (tableInput parameter completion (.position (.leaf lay tree leafIdx)))) (by
            simpa using hpending)
      exact havoids hslot.symm
  | node lay tree level nodeIdx =>
      have hnone : decodeProbe? parameter
          (tableInput parameter completion (.position (.node lay tree level nodeIdx))) = none := by
        simpa [tableInput, Position.domain] using
          (decodeProbe?_tweakableHashInput_of_not_chain_leaf parameter
            (.node lay tree (level.val + 1) nodeIdx.val)
            (tablePayload completion (.node lay tree level nodeIdx))
            (Position.domain_inRange (.node lay tree level nodeIdx))
            (by simp) (by simp))
      rw [heq] at hdecode
      exact (by simp [hdecode] at hnone)
  | ftsLeaf | ftsNode | ftsRoots => simp [IsOtsPosition] at hots

theorem ChronologicalCacheAgrees.of_coreEq
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left right : DeferredContext} {cache : QueryCache HashSpec}
    (hagrees : ChronologicalCacheAgrees parameter table left cache)
    (heq : left.CoreEq right) :
    ChronologicalCacheAgrees parameter table right cache := by
  intro completion hcompletion position hots
  have hknown := hagrees completion (hcompletion.of_coreEq heq.symm) position hots
  unfold ResolveInputAgrees at hknown ⊢
  rw [← heq.positionValue_eq]
  exact hknown

theorem FixedResolvedInput.of_coreEq
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left right : DeferredContext} {input : HashInput} {output : HashOutput}
    (hfixed : FixedResolvedInput parameter table left input output)
    (heq : left.CoreEq right) :
    FixedResolvedInput parameter table right input output := by
  rcases hfixed with ⟨position, hots, hvalue, hinput⟩
  refine ⟨position, hots, ?_, ?_⟩
  · rw [← heq.positionValue_eq]
    exact hvalue
  · intro completion hcompletion
    exact hinput completion (hcompletion.of_coreEq heq.symm)

theorem ResolvedCachePartition.of_coreEq
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left right : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table left ordinaryCache concreteCache)
    (heq : left.CoreEq right) :
    ResolvedCachePartition parameter table right ordinaryCache concreteCache := by
  refine ⟨hpartition.1, ?_⟩
  intro input output hcached
  rcases hpartition.2 input output hcached with hordinary | hfixed
  · exact Or.inl hordinary
  · exact Or.inr (hfixed.of_coreEq heq)

theorem resolvedCachePartition_empty (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) :
    ResolvedCachePartition parameter table
      { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        values := emptyDeferredStructuralValues }
      (∅ : QueryCache HashSpec) ∅ := by
  constructor
  · intro input output hcached
    simp at hcached
  · intro input output hcached
    simp at hcached

theorem ResolvedCachePartition.eq_of_stable
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table context ordinaryCache concreteCache)
    (hcompletable : DeferredCompletable table context)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ordinaryCache input = concreteCache input := by
  cases hordinary : ordinaryCache input with
  | some output =>
      exact (hpartition.1 input output hordinary).symm
  | none =>
      cases hconcrete : concreteCache input with
      | none => rfl
      | some output =>
          rcases hpartition.2 input output hconcrete with hcached |
            ⟨position, hots, _hvalue, hinput⟩
          · simp [hordinary] at hcached
          · obtain ⟨completion, hcompletion⟩ := hcompletable
            have hdecoded : decodePosition? parameter input = some position := by
              rw [hinput completion hcompletion]
              exact (decodePosition?_eq_some_iff parameter _ position).2
                ⟨tablePayload completion position, rfl⟩
            exact (hstable.2 position hdecoded hots).elim

theorem ResolvedCachePartition.eq_of_completionOrdinary
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table context ordinaryCache concreteCache)
    (hcompletable : DeferredCompletable table context)
    (input : HashInput)
    (hordinary : CompletionOrdinaryInput parameter table context input) :
    ordinaryCache input = concreteCache input := by
  cases hordinaryCache : ordinaryCache input with
  | some output => exact (hpartition.1 input output hordinaryCache).symm
  | none =>
      cases hconcrete : concreteCache input with
      | none => rfl
      | some output =>
          rcases hpartition.2 input output hconcrete with hcached |
            ⟨position, hots, _hvalue, hinput⟩
          · simp [hordinaryCache] at hcached
          · obtain ⟨completion, hcompletion⟩ := hcompletable
            exact (hordinary completion hcompletion position hots
              (hinput completion hcompletion)).elim

theorem FixedResolvedInput.of_resolveDeferredPositionValue
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {input : HashInput} {output : HashOutput}
    (hfixed : FixedResolvedInput parameter table context input output)
    (hvalid : context.Valid) (target : Position) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue target context)) :
    FixedResolvedInput parameter table result.toDeferredContext input output := by
  rcases hfixed with ⟨position, hots, hvalue, hinput⟩
  refine ⟨position, hots,
    resolveDeferredPositionValue_preserves_positionValue target position context result output
      hvalue hresult, ?_⟩
  intro completion hcompletion
  exact hinput completion
    (hcompletion.of_resolveDeferredPositionValue hvalid target result hresult)

theorem FixedResolvedInput.of_resolveDeferredChainStart
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {input : HashInput} {output : HashOutput}
    (hfixed : FixedResolvedInput parameter table context input output)
    (hagrees : StartTableAgrees context.state table) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    FixedResolvedInput parameter table result.toDeferredContext input output := by
  rcases hfixed with ⟨position, hots, hvalue, hinput⟩
  refine ⟨position, hots,
    resolveDeferredChainStart_preserves_positionValue table index context result position output
      hvalue hresult, ?_⟩
  intro completion hcompletion
  exact hinput completion
    (hcompletion.of_resolveDeferredChainStart hagrees index result hresult)

theorem FixedResolvedInput.of_materializeResolvedPosition
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {input : HashInput} {output : HashOutput}
    (position : Position) (result : DeferredResolution)
    (hfixed : FixedResolvedInput parameter table result.toDeferredContext input output)
    (hstateValues : result.state.values = context.state.values)
    (hpending : result.state.pending ⊆
      context.state.pendingAway (.position position))
    (hresolved : result.toDeferredContext.positionValue position = some result.output) :
    FixedResolvedInput parameter table
      (materializeResolvedPosition context position result) input output := by
  rcases hfixed with ⟨fixedPosition, hots, hvalue, hinput⟩
  refine ⟨fixedPosition, hots, ?_, ?_⟩
  · rw [materializeResolvedPosition_positionValue_eq context position result hstateValues
      hresolved]
    exact hvalue
  · intro completion hcompletion
    exact hinput completion
      (hcompletion.of_materializeResolvedPosition position result hstateValues hpending hresolved)

theorem FixedResolvedInput.of_materializeResolvedChainStart
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {input : HashInput} {output : HashOutput}
    (hfixed : FixedResolvedInput parameter table context input output)
    (hagrees : StartTableAgrees context.state table)
    (hcompletable : DeferredCompletable table context) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    FixedResolvedInput parameter table
      (materializeResolvedChainStart context index result) input output := by
  rcases hfixed with ⟨position, hots, hvalue, hinput⟩
  refine ⟨position, hots, ?_, ?_⟩
  · rw [materializeResolvedChainStart_positionValue_eq table index context result hresult]
    exact hvalue
  · intro completion hcompletion
    exact hinput completion
      (hcompletion.of_materializeResolvedChainStart hagrees index hcompletable result hresult)

theorem ResolvedCachePartition.of_materializeResolvedChainStart
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table context ordinaryCache concreteCache)
    (hagrees : StartTableAgrees context.state table)
    (hcompletable : DeferredCompletable table context) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    ResolvedCachePartition parameter table
      (materializeResolvedChainStart context index result) ordinaryCache concreteCache := by
  refine ⟨hpartition.1, ?_⟩
  intro input output hcached
  rcases hpartition.2 input output hcached with hordinary | hfixed
  · exact Or.inl hordinary
  · exact Or.inr (hfixed.of_materializeResolvedChainStart hagrees hcompletable index result
      hresult)

theorem ResolvedCachePartition.of_resolveDeferredChainStart
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table context ordinaryCache concreteCache)
    (hagrees : StartTableAgrees context.state table) (index : OtsSecretIndex)
    (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    ResolvedCachePartition parameter table result.toDeferredContext ordinaryCache concreteCache := by
  refine ⟨hpartition.1, ?_⟩
  intro input output hcached
  rcases hpartition.2 input output hcached with hordinary | hfixed
  · exact Or.inl hordinary
  · exact Or.inr (hfixed.of_resolveDeferredChainStart hagrees index result hresult)

theorem fixedResolvedInput_of_resolveDeferredPositionValue
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} (position : Position) (input : HashInput)
    (hots : IsOtsPosition position)
    (hcanonical : ∀ completion, DeferredCompletion table context completion →
      input = tableInput parameter completion (.position position))
    (hvalid : context.Valid) (result : DeferredResolution)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context)) :
    FixedResolvedInput parameter table result.toDeferredContext input result.output := by
  refine ⟨position, hots,
    resolveDeferredPositionValue_resolves position context result hresult, ?_⟩
  intro completion hcompletion
  exact hcanonical completion
    (hcompletion.of_resolveDeferredPositionValue hvalid position result hresult)

theorem ResolvedCachePartition.of_resolveDeferredPositionValue
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table context ordinaryCache concreteCache)
    (hcache : ChronologicalCacheAgrees parameter table context concreteCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (position : Position) (input : HashInput)
    (hots : IsOtsPosition position)
    (hcanonical : ∀ completion, DeferredCompletion table context completion →
      input = tableInput parameter completion (.position position))
    (result : DeferredResolution) (output : HashOutput)
    (finalCache : QueryCache HashSpec)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position context))
    (hquery : ResolveQueryRel input concreteCache (some result) (output, finalCache)) :
    ResolvedCachePartition parameter table result.toDeferredContext ordinaryCache finalCache := by
  rcases hquery with ⟨houtput, rfl⟩
  subst output
  have hnewFixed := fixedResolvedInput_of_resolveDeferredPositionValue position input hots
    hcanonical hvalid result hresult
  constructor
  · intro other cached hordinary
    have hc_cached := hpartition.1 other cached hordinary
    by_cases heq : other = input
    · subst other
      obtain ⟨completion, hcompletion⟩ := hcompletable
      have hagrees := hcache completion hcompletion position hots
      rw [← hcanonical completion hcompletion] at hagrees
      unfold ResolveInputAgrees at hagrees
      cases hvalue : context.positionValue position with
      | none =>
          rw [hvalue] at hagrees
          rw [hc_cached] at hagrees
          simp at hagrees
      | some known =>
          rw [hvalue] at hagrees
          have hknownCached : known = cached := Option.some.inj (hagrees.symm.trans hc_cached)
          have hpreserved := resolveDeferredPositionValue_preserves_positionValue position
            position context result known hvalue hresult
          have hresolved := resolveDeferredPositionValue_resolves position context result hresult
          have hresultOutput : result.output = known :=
            Option.some.inj (hresolved.symm.trans hpreserved)
          simpa [QueryCache.cacheQuery_self, hresultOutput, hknownCached]
    · simpa [QueryCache.cacheQuery_of_ne concreteCache result.output heq] using hc_cached
  · intro other cached hfinal
    by_cases heq : other = input
    · subst other
      have hcached : cached = result.output := by
        simpa [QueryCache.cacheQuery_self] using hfinal.symm
      subst cached
      exact Or.inr hnewFixed
    · have hold : concreteCache other = some cached := by
        simpa [QueryCache.cacheQuery_of_ne concreteCache result.output heq] using hfinal
      rcases hpartition.2 other cached hold with hordinary | hfixed
      · exact Or.inl hordinary
      · exact Or.inr (hfixed.of_resolveDeferredPositionValue hvalid position result hresult)

def ResolvedContextInvariant (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (ordinaryCache concreteCache : QueryCache HashSpec) : Prop :=
  ChronologicalCacheAgrees parameter table context concreteCache ∧
    context.Valid ∧
    StartTableAgrees context.state table ∧
    DeferredCompletable table context ∧
    ResolvedCachePartition parameter table context ordinaryCache concreteCache

theorem ResolvedContextInvariant.of_coreEq
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left right : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table left ordinaryCache concreteCache)
    (heq : left.CoreEq right) :
    ResolvedContextInvariant parameter table right ordinaryCache concreteCache := by
  rcases hinvariant with ⟨hcache, hvalid, hstarts, hcompletable, hpartition⟩
  exact ⟨hcache.of_coreEq heq, hvalid.of_coreEq heq, hstarts.of_coreEq heq,
    (deferredCompletable_iff_of_coreEq heq).mp hcompletable,
    hpartition.of_coreEq heq⟩

theorem ResolvedContextInvariant.addPending_of_completable
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (coordinate : Coordinate) (candidate : Digest)
    (hcompletable : DeferredCompletable table
      { context with state := context.state.addPending coordinate candidate }) :
    ResolvedContextInvariant parameter table
      { context with state := context.state.addPending coordinate candidate }
      ordinaryCache concreteCache := by
  rcases hinvariant with ⟨hcache, hvalid, hstarts, _, hpartition⟩
  obtain ⟨completion, hcompletion⟩ := hcompletable
  refine ⟨?_, ?_, hstarts.addPending coordinate candidate, ⟨completion, hcompletion⟩, ?_⟩
  · intro otherCompletion hotherCompletion position hots
    have horiginal := hotherCompletion.of_addPending coordinate candidate
    have hknown := hcache otherCompletion horiginal position hots
    unfold ResolveInputAgrees at hknown ⊢
    simpa [DeferredContext.positionValue, LazyRevealProbe.State.addPending] using
      hknown
  · refine ⟨hvalid.valuesConsistent.addPending coordinate candidate, ?_⟩
    intro other output hvalue
    have hvalueOriginal : context.state.values other = some output := by
      simpa [LazyRevealProbe.State.addPending] using hvalue
    have hcompletionValue : completion other = output :=
      hcompletion.1 other output hvalueOriginal
    intro hhit
    unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt at hhit
    rw [Finset.mem_image] at hhit
    obtain ⟨⟨hitCoordinate, hitCandidate⟩, hentry, hcandidate⟩ := hhit
    simp only [Finset.mem_filter, LazyRevealProbe.State.addPending,
      Finset.mem_insert] at hentry
    rcases hentry with ⟨hnew | hold, hcoordinate⟩
    · cases hnew
      have havoids := hcompletion.2.2.1 coordinate candidate (by
        simp [LazyRevealProbe.State.addPending])
      apply havoids
      rw [hcoordinate, hcompletionValue]
      exact hcandidate.symm
    · apply hvalid.2 other output hvalueOriginal
      unfold LazyRevealProbe.State.hitAt LazyRevealProbe.State.pendingAt
      rw [Finset.mem_image]
      exact ⟨(hitCoordinate, hitCandidate), by
        simp only [Finset.mem_filter]
        exact ⟨hold, hcoordinate⟩, hcandidate⟩
  · refine ⟨hpartition.1, ?_⟩
    intro input output hcached
    rcases hpartition.2 input output hcached with hordinary | hfixed
    · exact Or.inl hordinary
    · rcases hfixed with ⟨position, hots, hvalue, hinput⟩
      exact Or.inr ⟨position, hots, by
        simpa [DeferredContext.positionValue, LazyRevealProbe.State.addPending] using hvalue,
        fun otherCompletion hotherCompletion =>
          hinput otherCompletion
            (hotherCompletion.of_addPending coordinate candidate)⟩

theorem ResolvedAdministrative.run_preserves_invariant
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {value : alpha} (hadministrative : ResolvedAdministrative computation value)
    (context : DeferredContext) (cache : SplitHashCache) (fuel : Nat)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    ∃ finalContext,
      runResolvedFromTable context fuel table (computation.run cache) =
        pure (some ⟨finalContext, fuel, (value, cache), table⟩) ∧
      ResolvedContextInvariant parameter table finalContext
        (ordinaryQueryCache cache) concreteCache := by
  obtain ⟨finalContext, hrun, hpending, hvalues, hprivate⟩ :=
    hadministrative.run context cache fuel table
  have hcore : context.CoreEq finalContext :=
    ⟨hpending.symm, hvalues.symm, hprivate.symm⟩
  exact ⟨finalContext, hrun, hinvariant.of_coreEq hcore⟩

theorem ResolvedContextInvariant.materialize_resolvedChainStart
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (index : OtsSecretIndex) (result : DeferredResolution)
    (hresult : resolveDeferredChainStart table index context = some result) :
    ResolvedContextInvariant parameter table
      (materializeResolvedChainStart context index result) ordinaryCache concreteCache := by
  rcases hinvariant with ⟨hcache, hvalid, hstarts, hcompletable, hpartition⟩
  have houtput := resolveDeferredChainStart_output_of_agrees table index context result hstarts
    hresult
  refine ⟨?_, ?_, ?_, hcompletable.materializeResolvedChainStart hstarts index result hresult,
    hpartition.of_materializeResolvedChainStart hstarts hcompletable index result hresult⟩
  · intro completion hcompletion position hots
    have horiginal := hcompletion.of_materializeResolvedChainStart hstarts index hcompletable
      result hresult
    have hcurrent := hcache completion horiginal position hots
    unfold ResolveInputAgrees at hcurrent ⊢
    rw [materializeResolvedChainStart_positionValue_eq table index context result hresult]
    exact hcurrent
  · rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    have hdeferred := resolveDeferredChainStart_deferred_values_eq table
      ⟨lay, tree, leafIdx, chainIdx⟩ context result hresult
    unfold materializeResolvedChainStart
    rw [hdeferred]
    exact hvalid.materialize_chainStart lay tree leafIdx chainIdx result.output
  · unfold materializeResolvedChainStart
    rw [houtput]
    exact hstarts.materialize_start index

theorem ResolvedContextInvariant.materialize_chainStart
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (index : OtsSecretIndex) :
    ResolvedContextInvariant parameter table
      { state := context.state.materialize index.coordinate (table index)
        values := context.values }
      ordinaryCache concreteCache := by
  have hclean := hinvariant.2.2.2.1.not_hitAt_chainStart index
  cases hvalue : context.state.values index.coordinate with
  | some output =>
      have houtput := hinvariant.2.2.1 index output hvalue
      let result : DeferredResolution :=
        ⟨{ state := context.state.clearPending index.coordinate, values := context.values },
          table index⟩
      have hresult : resolveDeferredChainStart table index context = some result := by
        simp [resolveDeferredChainStart, hvalue, houtput, hclean, result]
      have hresolved := hinvariant.materialize_resolvedChainStart index result hresult
      simpa [materializeResolvedChainStart, result] using hresolved
  | none =>
      let result : DeferredResolution :=
        ⟨{ state := context.state.clearPending index.coordinate, values := context.values },
          table index⟩
      have hresult : resolveDeferredChainStart table index context = some result := by
        simp [resolveDeferredChainStart, hvalue, hclean, result]
      have hresolved := hinvariant.materialize_resolvedChainStart index result hresult
      simpa [materializeResolvedChainStart, result] using hresolved

theorem ChronologicalCacheAgrees.of_materializeResolvedPosition
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (position : Position) (result : DeferredResolution)
    (hagrees : ChronologicalCacheAgrees parameter table result.toDeferredContext cache)
    (hstateValues : result.state.values = context.state.values)
    (hpending : result.state.pending ⊆
      context.state.pendingAway (.position position))
    (hresolved : result.toDeferredContext.positionValue position = some result.output) :
    ChronologicalCacheAgrees parameter table
      (materializeResolvedPosition context position result) cache := by
  intro completion hcompletion other hots
  have hcompletionResult := hcompletion.of_materializeResolvedPosition position result
    hstateValues hpending hresolved
  have hcurrent := hagrees completion hcompletionResult other hots
  unfold ResolveInputAgrees at hcurrent ⊢
  rw [materializeResolvedPosition_positionValue_eq context position result hstateValues
    hresolved]
  exact hcurrent

theorem ResolvedCachePartition.of_materializeResolvedPosition
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (position : Position) (result : DeferredResolution)
    (hpartition : ResolvedCachePartition parameter table result.toDeferredContext
      ordinaryCache concreteCache)
    (hstateValues : result.state.values = context.state.values)
    (hpending : result.state.pending ⊆
      context.state.pendingAway (.position position))
    (hresolved : result.toDeferredContext.positionValue position = some result.output) :
    ResolvedCachePartition parameter table
      (materializeResolvedPosition context position result) ordinaryCache concreteCache := by
  refine ⟨hpartition.1, ?_⟩
  intro input output hcached
  rcases hpartition.2 input output hcached with hordinary | hfixed
  · exact Or.inl hordinary
  · exact Or.inr (hfixed.of_materializeResolvedPosition position result hstateValues
      hpending hresolved)

theorem DeferredContext.Valid.materializeResolvedPosition_of
    {context : DeferredContext} (hvalid : context.Valid) (position : Position)
    (result : DeferredResolution) (hresultValid : result.toDeferredContext.Valid)
    (hstateValues : result.state.values = context.state.values)
    (hresolved : result.toDeferredContext.positionValue position = some result.output) :
    (materializeResolvedPosition context position result).Valid := by
  have htemporary :
      ({ state := context.state, values := result.values } : DeferredContext).Valid := by
    constructor
    · intro other output hvalue
      apply hresultValid.1 other output
      rw [hstateValues]
      exact hvalue
    · exact hvalid.2
  have hprivate : result.values position = some result.output := by
    unfold DeferredContext.positionValue at hresolved
    rw [hstateValues] at hresolved
    cases hstate : context.state.values (.position position) with
    | none => simpa [hstate] using hresolved
    | some output =>
        have hsame : output = result.output := by simpa [hstate] using hresolved
        simpa [hsame] using hresultValid.1 position output (by
          rw [hstateValues]
          exact hstate)
  exact htemporary.materialize_position position result.output hprivate

theorem ResolvedContextInvariant.materialize_resolvedReveal
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinitial : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredReveal table position context))
    {finalCache : QueryCache HashSpec}
    (hresultInvariant : ResolvedContextInvariant parameter table result.toDeferredContext
      ordinaryCache finalCache)
    (hcompletable : DeferredCompletable table
      (materializeResolvedPosition context position result)) :
    ResolvedContextInvariant parameter table
      (materializeResolvedPosition context position result) ordinaryCache finalCache := by
  rcases hinitial with ⟨_initialCache, hvalid, hstarts, _initialCompletable,
    _initialPartition⟩
  rcases hresultInvariant with ⟨hcache, hresultValid, _resultStarts,
    _resultCompletable, hpartition⟩
  have hstateValues := resolveDeferredReveal_preserves_state_values table position context result
    hresult
  have hpending := resolveDeferredReveal_pendingAway_subset table position context result hresult
  have hresolved := resolveDeferredReveal_resolves table position context result hresult
  exact ⟨
    hcache.of_materializeResolvedPosition position result hstateValues hpending hresolved,
    hvalid.materializeResolvedPosition_of position result hresultValid hstateValues hresolved,
    by simpa [materializeResolvedPosition] using
      hstarts.materialize_position position result.output,
    hcompletable,
    hpartition.of_materializeResolvedPosition position result hstateValues hpending hresolved⟩

theorem ChronologicalCacheAgrees.of_stable_cacheQuery
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hagrees : ChronologicalCacheAgrees parameter table context cache)
    (input : HashInput) (output : HashOutput)
    (hstable : StableOrdinaryInput parameter input) :
    ChronologicalCacheAgrees parameter table context (cache.cacheQuery input output) := by
  intro completion hcompletion position hots
  have hcurrent := hagrees completion hcompletion position hots
  have hdecoded : decodePosition? parameter
      (tableInput parameter completion (.position position)) = some position :=
    (decodePosition?_eq_some_iff parameter _ position).2
      ⟨tablePayload completion position, rfl⟩
  have hne : tableInput parameter completion (.position position) ≠ input := by
    intro heq
    rw [heq] at hdecoded
    exact hstable.2 position hdecoded hots
  unfold ResolveInputAgrees at hcurrent ⊢
  cases hvalue : context.positionValue position <;> rw [hvalue] at hcurrent
  · change cache.cacheQuery input output
        (tableInput parameter completion (.position position)) = none
    rw [QueryCache.cacheQuery_of_ne cache output hne]
    simpa only using hcurrent
  · change cache.cacheQuery input output
        (tableInput parameter completion (.position position)) = some _
    rw [QueryCache.cacheQuery_of_ne cache output hne]
    simpa only using hcurrent

theorem ChronologicalCacheAgrees.of_completionOrdinary_cacheQuery
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {cache : QueryCache HashSpec}
    (hagrees : ChronologicalCacheAgrees parameter table context cache)
    (input : HashInput) (output : HashOutput)
    (hordinary : CompletionOrdinaryInput parameter table context input) :
    ChronologicalCacheAgrees parameter table context (cache.cacheQuery input output) := by
  intro completion hcompletion position hots
  have hcurrent := hagrees completion hcompletion position hots
  have hne := (hordinary completion hcompletion position hots).symm
  unfold ResolveInputAgrees at hcurrent ⊢
  cases hvalue : context.positionValue position <;> rw [hvalue] at hcurrent
  · change cache.cacheQuery input output
        (tableInput parameter completion (.position position)) = none
    rw [QueryCache.cacheQuery_of_ne cache output hne]
    simpa only using hcurrent
  · change cache.cacheQuery input output
        (tableInput parameter completion (.position position)) = some _
    rw [QueryCache.cacheQuery_of_ne cache output hne]
    simpa only using hcurrent

theorem ResolvedCachePartition.cacheQuery
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table context ordinaryCache concreteCache)
    (input : HashInput) (output : HashOutput) :
    ResolvedCachePartition parameter table context
      (ordinaryCache.cacheQuery input output) (concreteCache.cacheQuery input output) := by
  constructor
  · intro other cached hordinary
    by_cases heq : other = input
    · subst other
      have hcached : cached = output := by
        simpa [QueryCache.cacheQuery_self] using hordinary.symm
      subst cached
      simp [QueryCache.cacheQuery_self]
    · have hold : ordinaryCache other = some cached := by
        simpa [QueryCache.cacheQuery_of_ne ordinaryCache output heq] using hordinary
      have hconcrete := hpartition.1 other cached hold
      simpa [QueryCache.cacheQuery_of_ne concreteCache output heq] using hconcrete
  · intro other cached hconcrete
    by_cases heq : other = input
    · subst other
      have hcached : cached = output := by
        simpa [QueryCache.cacheQuery_self] using hconcrete.symm
      subst cached
      exact Or.inl (by simp [QueryCache.cacheQuery_self])
    · have hold : concreteCache other = some cached := by
        simpa [QueryCache.cacheQuery_of_ne concreteCache output heq] using hconcrete
      rcases hpartition.2 other cached hold with hordinary | hfixed
      · exact Or.inl (by
          simpa [QueryCache.cacheQuery_of_ne ordinaryCache output heq] using hordinary)
      · exact Or.inr hfixed

theorem ResolvedCachePartition.cacheLeft_of_concrete
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hpartition : ResolvedCachePartition parameter table context ordinaryCache concreteCache)
    (input : HashInput) (output : HashOutput)
    (hconcrete : concreteCache input = some output) :
    ResolvedCachePartition parameter table context
      (ordinaryCache.cacheQuery input output) concreteCache := by
  constructor
  · intro other cached hordinary
    by_cases heq : other = input
    · subst other
      have hcached : cached = output := by
        simpa [QueryCache.cacheQuery_self] using hordinary.symm
      simpa [hcached] using hconcrete
    · have hold : ordinaryCache other = some cached := by
        simpa [QueryCache.cacheQuery_of_ne ordinaryCache output heq] using hordinary
      exact hpartition.1 other cached hold
  · intro other cached hcached
    rcases hpartition.2 other cached hcached with hordinary | hfixed
    · by_cases heq : other = input
      · subst other
        have hvalue : cached = output := by
          rw [hconcrete] at hcached
          exact Option.some.inj hcached.symm
        exact Or.inl (by simp [hvalue, QueryCache.cacheQuery_self])
      · exact Or.inl (by
          simpa [QueryCache.cacheQuery_of_ne ordinaryCache output heq] using hordinary)
    · exact Or.inr hfixed

theorem ResolvedContextInvariant.cacheLeft_of_concrete
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (input : HashInput) (output : HashOutput)
    (hconcrete : concreteCache input = some output) :
    ResolvedContextInvariant parameter table context
      (ordinaryCache.cacheQuery input output) concreteCache := by
  exact ⟨hinvariant.1, hinvariant.2.1, hinvariant.2.2.1, hinvariant.2.2.2.1,
    hinvariant.2.2.2.2.cacheLeft_of_concrete input output hconcrete⟩

theorem ResolvedContextInvariant.concreteCache_eq_of_positionValue
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (position : Position) (hots : IsOtsPosition position)
    (output : HashOutput) (hvalue : context.positionValue position = some output)
    (input : HashInput)
    (hcanonical : ∀ completion, DeferredCompletion table context completion →
      input = tableInput parameter completion (.position position)) :
    concreteCache input = some output := by
  obtain ⟨completion, hcompletion⟩ := hinvariant.2.2.2.1
  have hknown := hinvariant.1 completion hcompletion position hots
  unfold ResolveInputAgrees at hknown
  rw [hvalue] at hknown
  rw [hcanonical completion hcompletion]
  exact hknown

noncomputable def publishOrdinaryInput
    (coordinate : Coordinate) (input : HashInput) (output : HashOutput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput := do
  publishCoordinate coordinate
  modify fun cache : SplitHashCache =>
    Function.update cache (.ordinary input) (some output)
  pure output

theorem ResolvedContextInvariant.of_stable_cacheQuery
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (input : HashInput) (output : HashOutput)
    (hstable : StableOrdinaryInput parameter input) :
    ResolvedContextInvariant parameter table context
      (ordinaryCache.cacheQuery input output) (concreteCache.cacheQuery input output) := by
  rcases hinvariant with ⟨hcache, hvalid, hstarts, hcompletable, hpartition⟩
  exact ⟨hcache.of_stable_cacheQuery input output hstable, hvalid, hstarts, hcompletable,
    hpartition.cacheQuery input output⟩

theorem ResolvedContextInvariant.of_completionOrdinary_cacheQuery
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache concreteCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache concreteCache)
    (input : HashInput) (output : HashOutput)
    (hordinary : CompletionOrdinaryInput parameter table context input) :
    ResolvedContextInvariant parameter table context
      (ordinaryCache.cacheQuery input output) (concreteCache.cacheQuery input output) := by
  exact ⟨hinvariant.1.of_completionOrdinary_cacheQuery input output hordinary,
    hinvariant.2.1, hinvariant.2.2.1, hinvariant.2.2.2.1,
    hinvariant.2.2.2.2.cacheQuery input output⟩

def ResolvePositionRel (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ordinaryCache : QueryCache HashSpec)
    (position : Position) :
    Option DeferredResolution → Digest × QueryCache HashSpec → Prop
  | none, _ => True
  | some resolved, (value, cache) =>
      value = truncateHash resolved.output ∧
        ResolvedContextInvariant parameter table resolved.toDeferredContext ordinaryCache cache ∧
        resolved.toDeferredContext.positionValue position = some resolved.output

theorem relTriple_resolveDeferredPositionValue_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (context : DeferredContext)
    (ordinaryCache cache : QueryCache HashSpec)
    (input : HashInput)
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache cache)
    (hots : IsOtsPosition position)
    (hcanonical : ∀ completion, DeferredCompletion table context completion →
      input = tableInput parameter completion (.position position)) :
    RelTriple
      (resolveDeferredPositionValue position context)
      ((randomOracle input).run cache >>= fun result =>
        pure (truncateHash result.1, result.2))
      (ResolvePositionRel parameter table ordinaryCache position) := by
  rcases hinvariant with ⟨hcache, hvalid, hstarts, hcompletable, hpartition⟩
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hcompletableOriginal : DeferredCompletable table context := ⟨completion, hcompletion⟩
  have hagrees := hcache completion hcompletion position hots
  rw [← hcanonical completion hcompletion] at hagrees
  have hquery := relTriple_resolveDeferredPositionValue_of_inputAgrees
    position context input cache hagrees
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hquery
      (fun resolved => resolved ∈ support (resolveDeferredPositionValue position context))
      (fun resolved hresolved => hresolved)
  have hbound : RelTriple
      (resolveDeferredPositionValue position context >>= fun resolved => pure resolved)
      ((randomOracle input).run cache >>= fun result =>
        pure (truncateHash result.1, result.2))
      (ResolvePositionRel parameter table ordinaryCache position) := by
    apply relTriple_bind hsupported
    intro resolved queryResult hrelation
    rcases hrelation with ⟨hqueryRel, hresultSupport⟩
    apply relTriple_pure_pure
    cases resolved with
    | none => trivial
    | some resolved =>
        rcases queryResult with ⟨output, finalCache⟩
        refine ⟨congrArg truncateHash hqueryRel.1 |>.symm, ⟨
          hcache.of_resolveDeferredPositionValue hvalid position input hcanonical
            resolved output finalCache hresultSupport hqueryRel,
          hvalid.of_resolveDeferredPositionValue position resolved hresultSupport,
          ?_,
          hcompletableOriginal.of_resolveDeferredPositionValue hvalid position resolved
            hresultSupport,
          hpartition.of_resolveDeferredPositionValue hcache hvalid hcompletableOriginal
            position input hots hcanonical resolved output finalCache hresultSupport hqueryRel⟩,
          resolveDeferredPositionValue_resolves position context resolved hresultSupport⟩
        intro index cached hvalue
        apply hstarts index cached
        rw [← resolveDeferredPositionValue_preserves_state_values position context resolved
          hresultSupport]
        exact hvalue
  simpa using hbound

def ResolvedChainInvariant (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (ordinaryCache : QueryCache HashSpec) (steps : Nat)
    (resolved : DeferredResolution) (cache : QueryCache HashSpec) : Prop :=
  ResolvedContextInvariant parameter table resolved.toDeferredContext ordinaryCache cache ∧
    ((steps = 0 ∧ resolved.output = table ⟨lay, tree, leafIdx, chainIdx⟩) ∨
      ∃ previous : ChainStep, steps = previous.val + 1 ∧
        resolved.toDeferredContext.positionValue
          (.chain lay tree leafIdx chainIdx previous) = some resolved.output)

theorem chainInput_eq_tableInput_of_completion
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (steps : Nat) (hsteps : steps < chainLength - 1) (output : HashOutput)
    (context : DeferredContext) (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion)
    (htip : (steps = 0 ∧ output = table ⟨lay, tree, leafIdx, chainIdx⟩) ∨
      ∃ previous : ChainStep, steps = previous.val + 1 ∧
        context.positionValue (.chain lay tree leafIdx chainIdx previous) = some output) :
    tweakableHashInput parameter (.chain lay tree leafIdx chainIdx ⟨steps, hsteps⟩)
        (digestBytes (truncateHash output)) =
      tableInput parameter completion
        (.position (.chain lay tree leafIdx chainIdx ⟨steps, hsteps⟩)) := by
  rcases htip with ⟨hzero, houtput⟩ | ⟨source, hsource, hvalue⟩
  · subst steps
    rw [houtput]
    have hstart := hcompletion.2.2.2 ⟨lay, tree, leafIdx, chainIdx⟩
    change completion (.chainStart lay tree leafIdx chainIdx) =
      table ⟨lay, tree, leafIdx, chainIdx⟩ at hstart
    simpa [tableInput, tablePayload, Position.domain] using
      congrArg (fun value => tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨0, hsteps⟩)
        (digestBytes (truncateHash value))) hstart.symm
  · have hpositive : 0 < steps := by omega
    have hnonzero : steps ≠ 0 := Nat.ne_of_gt hpositive
    have hsourceValue := hcompletion.eq_positionValue
      (.chain lay tree leafIdx chainIdx source) output hvalue
    have hsourceEq : (⟨steps - 1, by omega⟩ : ChainStep) = source := by
      apply Fin.ext
      change steps - 1 = source.val
      omega
    simp [tableInput, tablePayload, Position.children, hpositive, hsourceEq,
      hnonzero, tableValue, hsourceValue, Position.domain]

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredChainPrefix_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (context : DeferredContext) (ordinaryCache cache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache cache) :
    ∀ steps hsteps,
      RelTriple
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context)
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (chainWalk parameter lay tree leafIdx chainIdx 0 steps
            (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))).run cache)
        (ResolveChainRel
          (ResolvedChainInvariant parameter table lay tree leafIdx chainIdx ordinaryCache
            steps)) := by
  rcases hinvariant with ⟨hcache, hvalid, hstarts, hcompletable, hpartition⟩
  apply relTriple_resolveDeferredChainPrefix parameter table lay tree leafIdx chainIdx
    context cache (ResolvedChainInvariant parameter table lay tree leafIdx chainIdx ordinaryCache)
    hstarts
  · intro result hresult
    refine ⟨⟨hcache.of_resolveDeferredChainStart hstarts
        ⟨lay, tree, leafIdx, chainIdx⟩ result hresult,
      hvalid.of_resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ result hresult,
      ?_, hcompletable.of_resolveDeferredChainStart
        ⟨lay, tree, leafIdx, chainIdx⟩ result hresult,
      hpartition.of_resolveDeferredChainStart hstarts ⟨lay, tree, leafIdx, chainIdx⟩
        result hresult⟩, Or.inl ⟨rfl, ?_⟩⟩
    · intro index output hvalue
      apply hstarts index output
      rw [← resolveDeferredChainStart_state_values_eq table
        ⟨lay, tree, leafIdx, chainIdx⟩ context result hresult]
      exact hvalue
    · exact resolveDeferredChainStart_output_of_agrees table
        ⟨lay, tree, leafIdx, chainIdx⟩ context result hstarts hresult
  · intro steps hsteps previous middleCache hinvariant
    rcases hinvariant with
      ⟨⟨hpreviousCache, hpreviousValid, hpreviousStarts, hpreviousCompletable,
        _hpreviousPartition⟩, htip⟩
    obtain ⟨completion, hcompletion⟩ := hpreviousCompletable
    have hcanonical := chainInput_eq_tableInput_of_completion parameter table lay tree leafIdx
      chainIdx steps hsteps previous.output previous.toDeferredContext completion hcompletion htip
    have hknown := hpreviousCache completion hcompletion
      (.chain lay tree leafIdx chainIdx ⟨steps, hsteps⟩) (by simp [IsOtsPosition])
    rw [← hcanonical] at hknown
    exact hknown
  · intro steps hsteps previous middleCache result output finalCache hinvariant
      hresultSupport hquery
    rcases hinvariant with
      ⟨⟨hpreviousCache, hpreviousValid, hpreviousStarts, hpreviousCompletable,
        hpreviousPartition⟩, htip⟩
    let position : Position := .chain lay tree leafIdx chainIdx ⟨steps, hsteps⟩
    let input := tweakableHashInput parameter position.domain
      (digestBytes (truncateHash previous.output))
    have hcanonical : ∀ completion,
        DeferredCompletion table previous.toDeferredContext completion →
        input = tableInput parameter completion (.position position) := by
      intro completion hcompletion
      simpa [input, position, Position.domain] using
        chainInput_eq_tableInput_of_completion parameter table lay tree leafIdx chainIdx
          steps hsteps previous.output previous.toDeferredContext completion hcompletion htip
    have hquery' : ResolveQueryRel input middleCache (some result) (output, finalCache) := by
      simpa [input, position, Position.domain] using hquery
    refine ⟨⟨hpreviousCache.of_resolveDeferredPositionValue hpreviousValid position input
        hcanonical result output finalCache hresultSupport hquery',
      hpreviousValid.of_resolveDeferredPositionValue position result hresultSupport,
      ?_, hpreviousCompletable.of_resolveDeferredPositionValue hpreviousValid position result
        hresultSupport,
      hpreviousPartition.of_resolveDeferredPositionValue hpreviousCache hpreviousValid
        hpreviousCompletable position input (by simp [position, IsOtsPosition]) hcanonical
        result output finalCache hresultSupport hquery'⟩, Or.inr ⟨⟨steps, hsteps⟩, rfl, ?_⟩⟩
    · intro index cached hvalue
      apply hpreviousStarts index cached
      rw [← resolveDeferredPositionValue_preserves_state_values position
        previous.toDeferredContext result hresultSupport]
      exact hvalue
    · exact resolveDeferredPositionValue_resolves position previous.toDeferredContext result
        hresultSupport

theorem ResolvedChainInvariant.fullChain
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex} {chainIdx : ChainIndex}
    {ordinaryCache : QueryCache HashSpec} {resolved : DeferredResolution}
    {cache : QueryCache HashSpec}
    (hinvariant : ResolvedChainInvariant parameter table lay tree leafIdx chainIdx
      ordinaryCache (chainLength - 1) resolved cache) :
    ResolvedContextInvariant parameter table resolved.toDeferredContext ordinaryCache cache ∧
      resolved.toDeferredContext.positionValue
        (.chain lay tree leafIdx chainIdx Position.lastChainStep) = some resolved.output := by
  rcases hinvariant with ⟨hcontext, htip⟩
  refine ⟨hcontext, ?_⟩
  rcases htip with ⟨hzero, _houtput⟩ | ⟨previous, hprevious, hvalue⟩
  · norm_num [chainLength, winternitzBits] at hzero
  · have heq : previous = Position.lastChainStep := by
      apply Fin.ext
      change previous.val = chainLength - 2
      omega
    simpa [heq] using hvalue

def ResolveChainFamilyRel (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (ordinaryCache : QueryCache HashSpec)
    {n : Nat} (family : Fin n → ChainIndex) :
    Option DeferredContext → (Fin n → Digest) × QueryCache HashSpec → Prop
  | none, _ => True
  | some context, (values, cache) =>
      ResolvedContextInvariant parameter table context ordinaryCache cache ∧
        ∀ index, ∃ output,
          context.positionValue
              (.chain lay tree leafIdx (family index) Position.lastChainStep) = some output ∧
            values index = truncateHash output

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredChainFamily_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ∀ {n : Nat} (family : Fin n → ChainIndex)
      (context : DeferredContext) (ordinaryCache cache : QueryCache HashSpec),
      ResolvedContextInvariant parameter table context ordinaryCache cache →
      RelTriple
        (resolveDeferredChains table lay tree leafIdx (List.ofFn family) context)
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (sequenceFin fun index =>
            chainWalk parameter lay tree leafIdx (family index) 0 (chainLength - 1)
              (truncateHash (table ⟨lay, tree, leafIdx, family index⟩)))).run cache)
        (ResolveChainFamilyRel parameter table lay tree leafIdx ordinaryCache family)
  | 0, family, context, ordinaryCache, cache, hinvariant => by
      simp [resolveDeferredChains, sequenceFin, ResolveChainFamilyRel, hinvariant]
  | n + 1, family, context, ordinaryCache, cache, hinvariant => by
      rw [List.ofFn_succ, resolveDeferredChains, sequenceFin, simulateQ_bind,
        StateT.run_bind]
      have hhead := relTriple_resolveDeferredChainPrefix_chronological parameter table lay tree
        leafIdx (family 0) context ordinaryCache cache hinvariant (chainLength - 1) (by omega)
      apply relTriple_bind hhead
      intro headOption headResult hheadRelation
      cases headOption with
      | none =>
          rcases headResult with ⟨headValue, headCache⟩
          simp only
          let right : ProbComp ((Fin (n + 1) → Digest) × QueryCache HashSpec) :=
            ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (do
              let tail ← sequenceFin fun index : Fin n =>
                chainWalk parameter lay tree leafIdx (family index.succ) 0
                  (chainLength - 1)
                  (truncateHash (table ⟨lay, tree, leafIdx, family index.succ⟩))
              pure (Fin.cases headValue tail))).run headCache)
          have hbase := relTriple_true
            (pure (none : Option DeferredContext) : ProbComp (Option DeferredContext)) right
          have hsupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
              (fun result => result = none) (by
                intro result hresult
                simpa using hresult)
          apply relTriple_post_mono hsupported
          intro leftResult _ hrelation
          rw [hrelation.2]
          trivial
      | some head =>
          rcases headResult with ⟨headValue, headCache⟩
          rcases hheadRelation with ⟨hheadValue, hheadInvariant⟩
          have hheadFull := hheadInvariant.fullChain
          have htail := relTriple_resolveDeferredChainFamily_chronological parameter table lay tree
            leafIdx (fun index : Fin n => family index.succ) head.toDeferredContext ordinaryCache
              headCache hheadFull.1
          have htailSupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support htail
              (fun result => result ∈ support
                (resolveDeferredChains table lay tree leafIdx
                  (List.ofFn fun index : Fin n => family index.succ) head.toDeferredContext))
              (fun result hresult => hresult)
          have hbound : RelTriple
              (resolveDeferredChains table lay tree leafIdx
                  (List.ofFn fun index : Fin n => family index.succ) head.toDeferredContext >>=
                fun result => pure result)
              (((simulateQ (randomOracle : QueryImpl HashSpec _)
                  (sequenceFin fun index : Fin n =>
                    chainWalk parameter lay tree leafIdx (family index.succ) 0
                      (chainLength - 1)
                      (truncateHash (table ⟨lay, tree, leafIdx, family index.succ⟩)))).run
                headCache) >>= fun tail =>
                  pure (Fin.cases headValue tail.1, tail.2))
              (ResolveChainFamilyRel parameter table lay tree leafIdx ordinaryCache family) := by
            apply relTriple_bind htailSupported
            intro tailOption tailResult htailRelation
            rcases htailRelation with ⟨htailRel, htailSupport⟩
            apply relTriple_pure_pure
            cases tailOption with
            | none => trivial
            | some finalContext =>
                rcases tailResult with ⟨tailValues, finalCache⟩
                rcases htailRel with ⟨hfinalInvariant, htailValues⟩
                refine ⟨hfinalInvariant, ?_⟩
                intro index
                refine Fin.cases ?_ (fun tailIndex => ?_) index
                · refine ⟨head.output, ?_, ?_⟩
                  · exact resolveDeferredChains_preserves_positionValue table lay tree leafIdx
                      (List.ofFn fun index : Fin n => family index.succ) head.toDeferredContext
                      finalContext
                      (.chain lay tree leafIdx (family 0) Position.lastChainStep) head.output
                      hheadFull.2 htailSupport
                  · simpa using hheadValue
                · obtain ⟨output, hposition, hvalue⟩ := htailValues tailIndex
                  exact ⟨output, hposition, hvalue⟩
          simpa [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure] using hbound

theorem relTriple_resolveDeferredChains_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (ordinaryCache cache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache cache) :
    RelTriple
      (resolveDeferredChains table lay tree leafIdx
        (List.ofFn fun chainIdx : ChainIndex => chainIdx) context)
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (oneTimePublicKey parameter lay tree leafIdx
          (fun chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))).run cache)
      (ResolveChainFamilyRel parameter table lay tree leafIdx ordinaryCache
        (fun chainIdx : ChainIndex => chainIdx)) := by
  simpa [oneTimePublicKey] using
    relTriple_resolveDeferredChainFamily_chronological parameter table lay tree leafIdx
      (fun chainIdx : ChainIndex => chainIdx) context ordinaryCache cache hinvariant

theorem leafInput_eq_tableInput_of_completion
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (endpoints : ChainIndex → Digest)
    (hvalues : ∀ chainIdx, ∃ output,
      context.positionValue
          (.chain lay tree leafIdx chainIdx Position.lastChainStep) = some output ∧
        endpoints chainIdx = truncateHash output)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion) :
    tweakableHashInput parameter (.leaf lay tree leafIdx) (leafPayload endpoints) =
      tableInput parameter completion (.position (.leaf lay tree leafIdx)) := by
  have hendpoints : endpoints = fun chainIdx =>
      tableValue completion (.chain lay tree leafIdx chainIdx Position.lastChainStep) := by
    funext chainIdx
    obtain ⟨output, hposition, houtput⟩ := hvalues chainIdx
    rw [houtput, tableValue, hcompletion.eq_positionValue
      (.chain lay tree leafIdx chainIdx Position.lastChainStep) output hposition]
  rw [hendpoints]
  simp [tableInput, tablePayload, leafPayload, Position.children, Function.comp_def,
    Position.domain]

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredOtsLeaf_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (ordinaryCache cache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache cache) :
    RelTriple
      (resolveDeferredOtsLeaf table lay tree leafIdx context)
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (do
          let endpoints ← oneTimePublicKey parameter lay tree leafIdx
            (fun chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          leafHash parameter lay tree leafIdx endpoints)).run cache)
      (ResolvePositionRel parameter table ordinaryCache (.leaf lay tree leafIdx)) := by
  rw [resolveDeferredOtsLeaf, simulateQ_bind, StateT.run_bind]
  have hchains := relTriple_resolveDeferredChains_chronological parameter table lay tree leafIdx
    context ordinaryCache cache hinvariant
  apply relTriple_bind hchains
  intro chainsOption endpointsResult hchainsRelation
  cases chainsOption with
  | none =>
      simp only
      have hbase := relTriple_true
        (pure (none : Option DeferredResolution) : ProbComp (Option DeferredResolution))
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (leafHash parameter lay tree leafIdx endpointsResult.1)).run endpointsResult.2)
      have hsupported :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun result => result = none) (by
            intro result hresult
            simpa using hresult)
      apply relTriple_post_mono hsupported
      intro leftResult _ hrelation
      rw [hrelation.2]
      trivial
  | some chains =>
      rcases endpointsResult with ⟨endpoints, middleCache⟩
      rcases hchainsRelation with ⟨hmiddleInvariant, hvalues⟩
      let input := tweakableHashInput parameter (.leaf lay tree leafIdx) (leafPayload endpoints)
      have hcanonical : ∀ completion, DeferredCompletion table chains completion →
          input = tableInput parameter completion (.position (.leaf lay tree leafIdx)) := by
        intro completion hcompletion
        exact leafInput_eq_tableInput_of_completion parameter table lay tree leafIdx chains
          endpoints hvalues completion hcompletion
      have hquery := relTriple_resolveDeferredPositionValue_chronological parameter table
        (.leaf lay tree leafIdx) chains ordinaryCache middleCache input hmiddleInvariant
          (by trivial) hcanonical
      simpa [leafHash, tweakableHash, oracleHash, input, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure] using hquery

set_option maxRecDepth 100000 in
theorem nodeInput_eq_tableInput_of_completion
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level < maxLayerHeight)
    (hspan : 2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
    (context : DeferredContext) (leftValue rightValue : Digest)
    (leftOutput rightOutput : HashOutput)
    (hleft : context.positionValue
      (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)) = some leftOutput)
    (hright : context.positionValue
      (deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega)) = some rightOutput)
    (hleftValue : leftValue = truncateHash leftOutput)
    (hrightValue : rightValue = truncateHash rightOutput)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion) :
    tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
        (nodePayload leftValue rightValue) =
      tableInput parameter completion
        (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx))) := by
  have hnode : nodeIdx < 2 ^ maxLayerHeight := by
    have hpow : 0 < 2 ^ (level + 1) := pow_pos (by omega) _
    nlinarith
  have hpowTwo : 2 ≤ 2 ^ (level + 1) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ level + 1 by omega)
  have hleftIndex : 2 * nodeIdx < 2 ^ maxLayerHeight := by nlinarith
  have hrightIndex : 2 * nodeIdx + 1 < 2 ^ maxLayerHeight := by nlinarith
  have hleftCompletion := hcompletion.eq_positionValue
    (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)) leftOutput hleft
  have hrightCompletion := hcompletion.eq_positionValue
    (deferredTreePosition lay tree level (2 * nodeIdx + 1) (by omega)) rightOutput hright
  rw [hleftValue, hrightValue]
  cases level with
  | zero =>
      simp only [deferredTreePosition] at hleftCompletion hrightCompletion
      have hleftLeaf : leafOfNat (2 * nodeIdx) = ⟨2 * nodeIdx, hleftIndex⟩ := by
        apply Fin.ext
        simp [leafOfNat, Nat.mod_eq_of_lt hleftIndex]
      have hrightLeaf : leafOfNat (2 * nodeIdx + 1) = ⟨2 * nodeIdx + 1, hrightIndex⟩ := by
        apply Fin.ext
        simp [leafOfNat, Nat.mod_eq_of_lt hrightIndex]
      rw [hleftLeaf] at hleftCompletion
      rw [hrightLeaf] at hrightCompletion
      simp only [tableInput, tablePayload, Position.domain]
      rw [Position.children, dif_pos (by
        simpa [leafOfNat, Nat.mod_eq_of_lt hnode] using hrightIndex),
        dif_neg (show ¬0 < (⟨0, hlevel⟩ : Fin maxLayerHeight).val by simp)]
      simp [nodePayload, tableValue, hleftCompletion, hrightCompletion, leafOfNat,
        Nat.mod_eq_of_lt hnode]
  | succ previous =>
      simp only [deferredTreePosition] at hleftCompletion hrightCompletion
      have hleftLeaf : leafOfNat (2 * nodeIdx) = ⟨2 * nodeIdx, hleftIndex⟩ := by
        apply Fin.ext
        simp [leafOfNat, Nat.mod_eq_of_lt hleftIndex]
      have hrightLeaf : leafOfNat (2 * nodeIdx + 1) = ⟨2 * nodeIdx + 1, hrightIndex⟩ := by
        apply Fin.ext
        simp [leafOfNat, Nat.mod_eq_of_lt hrightIndex]
      rw [hleftLeaf] at hleftCompletion
      rw [hrightLeaf] at hrightCompletion
      simp only [tableInput, tablePayload, Position.domain]
      rw [Position.children, dif_pos (by
        simpa [leafOfNat, Nat.mod_eq_of_lt hnode] using hrightIndex),
        dif_pos (show 0 < (⟨previous + 1, hlevel⟩ : Fin maxLayerHeight).val by simp)]
      simp [nodePayload, tableValue, hleftCompletion, hrightCompletion, leafOfNat,
        Nat.mod_eq_of_lt hnode]

set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem relTriple_resolveDeferredTreeNode_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) :
    ∀ (level nodeIdx : Nat) (hlevel : level ≤ maxLayerHeight)
      (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
      (context : DeferredContext) (ordinaryCache cache : QueryCache HashSpec),
      ResolvedContextInvariant parameter table context ordinaryCache cache →
      RelTriple
        (resolveDeferredTreeNode table lay tree level nodeIdx hlevel context)
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeNode parameter lay tree
            (fun leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
            level nodeIdx)).run cache)
        (ResolvePositionRel parameter table ordinaryCache
          (deferredTreePosition lay tree level nodeIdx hlevel))
  | 0, nodeIdx, hlevel, _hspan, context, ordinaryCache, cache, hinvariant => by
      rw [treeNode_zero_eq]
      simpa [resolveDeferredTreeNode, deferredTreePosition] using
        relTriple_resolveDeferredOtsLeaf_chronological parameter table lay tree
          (leafOfNat nodeIdx) context ordinaryCache cache hinvariant
  | level + 1, nodeIdx, hlevel, hspan, context, ordinaryCache, cache, hinvariant => by
      have hlevelSmall : level < maxLayerHeight := by omega
      have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ maxLayerHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ level * (2 * (nodeIdx + 1)) := by
            exact Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ level * 2 * (nodeIdx + 1) := by ring
          _ ≤ 2 ^ maxLayerHeight := hspan
      have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ maxLayerHeight := by
        rw [pow_succ] at hspan
        have heq : 2 ^ level * (2 * nodeIdx + 1 + 1) =
            2 ^ level * 2 * (nodeIdx + 1) := by ring
        rw [heq]
        exact hspan
      rw [resolveDeferredTreeNode, treeNode_succ_eq, simulateQ_bind, StateT.run_bind]
      have hleft := relTriple_resolveDeferredTreeNode_chronological parameter table lay tree level
        (2 * nodeIdx) (by omega) hleftSpan context ordinaryCache cache hinvariant
      apply relTriple_bind hleft
      intro leftOption leftResult hleftRelation
      cases leftOption with
      | none =>
          rcases leftResult with ⟨leftValue, leftCache⟩
          simp only
          let right : ProbComp (Digest × QueryCache HashSpec) :=
            ((simulateQ (randomOracle : QueryImpl HashSpec _)
              (do
                let rightValue ← treeNode parameter lay tree
                  (fun leafIdx chainIdx =>
                    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
                  level (2 * nodeIdx + 1)
                tweakableHash parameter (.node lay tree (level + 1) nodeIdx)
                  (nodePayload leftValue rightValue))).run leftCache)
          have hbase := relTriple_true
            (pure (none : Option DeferredResolution) : ProbComp (Option DeferredResolution)) right
          have hsupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
              (fun result => result = none) (by
                intro result hresult
                simpa using hresult)
          apply relTriple_post_mono hsupported
          intro leftResult _ hrelation
          rw [hrelation.2]
          trivial
      | some left =>
          rcases leftResult with ⟨leftValue, leftCache⟩
          rcases hleftRelation with ⟨hleftValue, hleftInvariant, hleftPosition⟩
          rw [simulateQ_bind, StateT.run_bind]
          have hright := relTriple_resolveDeferredTreeNode_chronological parameter table lay tree
            level (2 * nodeIdx + 1) (by omega) hrightSpan left.toDeferredContext ordinaryCache
              leftCache hleftInvariant
          have hrightSupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hright
              (fun result => result ∈ support
                (resolveDeferredTreeNode table lay tree level (2 * nodeIdx + 1) (by omega)
                  left.toDeferredContext))
              (fun result hresult => hresult)
          apply relTriple_bind hrightSupported
          intro rightOption rightResult hrightRelation
          rcases hrightRelation with ⟨hrightRel, hrightSupport⟩
          cases rightOption with
          | none =>
              rcases rightResult with ⟨rightValue, rightCache⟩
              simp only
              let right : ProbComp (Digest × QueryCache HashSpec) :=
                ((simulateQ (randomOracle : QueryImpl HashSpec _)
                  (tweakableHash parameter (.node lay tree (level + 1) nodeIdx)
                    (nodePayload leftValue rightValue))).run rightCache)
              have hbase := relTriple_true
                (pure (none : Option DeferredResolution) : ProbComp (Option DeferredResolution))
                right
              have hsupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
                  (fun result => result = none) (by
                    intro result hresult
                    simpa using hresult)
              apply relTriple_post_mono hsupported
              intro leftResult _ hrelation
              rw [hrelation.2]
              trivial
          | some right =>
              rcases rightResult with ⟨rightValue, rightCache⟩
              rcases hrightRel with ⟨hrightValue, hrightInvariant, hrightPosition⟩
              have hleftAtRight := resolveDeferredTreeNode_preserves_positionValue table lay tree
                level (2 * nodeIdx + 1) (by omega) left.toDeferredContext right
                (deferredTreePosition lay tree level (2 * nodeIdx) (by omega)) left.output
                hleftPosition hrightSupport
              let position : Position :=
                .node lay tree ⟨level, hlevelSmall⟩ (leafOfNat nodeIdx)
              let input := tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
                (nodePayload leftValue rightValue)
              have hcanonical : ∀ completion,
                  DeferredCompletion table right.toDeferredContext completion →
                  input = tableInput parameter completion (.position position) := by
                intro completion hcompletion
                exact nodeInput_eq_tableInput_of_completion parameter table lay tree level nodeIdx
                  hlevelSmall hspan right.toDeferredContext leftValue rightValue left.output
                  right.output hleftAtRight hrightPosition hleftValue hrightValue completion
                  hcompletion
              have hquery := relTriple_resolveDeferredPositionValue_chronological parameter table
                position right.toDeferredContext ordinaryCache rightCache input hrightInvariant
                  (by simp [position, IsOtsPosition]) hcanonical
              simpa [deferredTreePosition, position, input, tweakableHash, oracleHash,
                simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure] using hquery

noncomputable def resolvedPositionComputation
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) :
    Position → OracleComp HashSpec Digest
  | .chain lay tree leafIdx chainIdx step =>
      chainWalk parameter lay tree leafIdx chainIdx 0 (step.val + 1)
        (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
  | .leaf lay tree leafIdx => do
      let endpoints ← oneTimePublicKey parameter lay tree leafIdx
        (fun chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
      leafHash parameter lay tree leafIdx endpoints
  | .node lay tree level nodeIdx =>
      treeNode parameter lay tree
        (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
        (level.val + 1) nodeIdx.val
  | _ => pure 0

def VisibleResolvedComputationsCached (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ position output, ResolvableOtsPosition position →
    context.state.values (.position position) = some output →
      CachedRun cache (fromCache cache)
          (resolvedPositionComputation parameter table position) ∧
        evalWithAnswerFn (fromCache cache)
            (resolvedPositionComputation parameter table position) = truncateHash output

theorem VisibleResolvedComputationsCached.mono
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {initial final : QueryCache HashSpec}
    (hclosed : VisibleResolvedComputationsCached parameter table context initial)
    (hle : initial ≤ final) :
    VisibleResolvedComputationsCached parameter table context final := by
  intro position output hresolvable hvalue
  obtain ⟨hcached, heval⟩ := hclosed position output hresolvable hvalue
  have hcachedFinal :=
    (hcached.changeAnswerFn (agreesWithFn_fromCache initial)
      (agreesWithFn_fromCache_of_le hle)).mono hle
  refine ⟨hcachedFinal, ?_⟩
  calc
    evalWithAnswerFn (fromCache final)
        (resolvedPositionComputation parameter table position) =
      evalWithAnswerFn (fromCache initial)
        (resolvedPositionComputation parameter table position) :=
      hcached.eval_eq (agreesWithFn_fromCache initial)
        (agreesWithFn_fromCache_of_le hle) |>.symm
    _ = truncateHash output := heval

theorem VisibleResolvedComputationsCached.of_state_values_eq
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left right : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : VisibleResolvedComputationsCached parameter table left cache)
    (hvalues : right.state.values = left.state.values) :
    VisibleResolvedComputationsCached parameter table right cache := by
  intro position output hresolvable hvalue
  apply hclosed position output hresolvable
  rw [← hvalues]
  exact hvalue

theorem VisibleResolvedComputationsCached.of_position_values_eq
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left right : DeferredContext} {cache : QueryCache HashSpec}
    (hclosed : VisibleResolvedComputationsCached parameter table left cache)
    (hvalues : ∀ position,
      right.state.values (.position position) = left.state.values (.position position)) :
    VisibleResolvedComputationsCached parameter table right cache := by
  intro position output hresolvable hvalue
  apply hclosed position output hresolvable
  rw [← hvalues]
  exact hvalue

theorem visibleResolvedComputationsCached_empty
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (values : DeferredStructuralValues) (cache : QueryCache HashSpec) :
    VisibleResolvedComputationsCached parameter table
      { state := LazyRevealProbe.State.empty, values := values } cache := by
  intro position output hresolvable hvalue
  simp [LazyRevealProbe.State.empty] at hvalue

theorem TableInputAvailable.changeTable
    {left right : Coordinate → HashOutput}
    {state : LazyRevealProbe.State Coordinate} {coordinate : Coordinate}
    (havailable : TableInputAvailable left state coordinate)
    (hagrees : ∀ other output, state.values other = some output → right other = output) :
    TableInputAvailable right state coordinate := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [TableInputAvailable] at havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hzero : step.val = 0
          · have hvalue : state.values (.chainStart lay tree leafIdx chainIdx) =
                some (left (.chainStart lay tree leafIdx chainIdx)) := by
              simpa [TableInputAvailable, hzero] using havailable
            simpa [TableInputAvailable, hzero, hagrees _ _ hvalue] using hvalue
          · have havailable' : ∀ child,
                child ∈ (Position.chain lay tree leafIdx chainIdx step).children →
                  state.values (.position child) = some (left (.position child)) := by
              simpa [TableInputAvailable, hzero] using havailable
            simp only [TableInputAvailable, if_neg hzero]
            intro child hchild
            have hvalue := havailable' child hchild
            simpa [hagrees _ _ hvalue] using hvalue
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          intro child hchild
          have hvalue := havailable child hchild
          simpa [hagrees _ _ hvalue] using hvalue

theorem tableInput_eq_of_available
    (parameter : PublicParameter) (left right : Coordinate → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (hleft : TableInputAvailable left state coordinate)
    (hright : TableInputAvailable right state coordinate) :
    tableInput parameter left coordinate = tableInput parameter right coordinate := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => simp [TableInputAvailable] at hleft
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          by_cases hzero : step.val = 0
          · have hleftValue : state.values (.chainStart lay tree leafIdx chainIdx) =
                some (left (.chainStart lay tree leafIdx chainIdx)) := by
              simpa [TableInputAvailable, hzero] using hleft
            have hrightValue : state.values (.chainStart lay tree leafIdx chainIdx) =
                some (right (.chainStart lay tree leafIdx chainIdx)) := by
              simpa [TableInputAvailable, hzero] using hright
            have heq := Option.some.inj (hleftValue.symm.trans hrightValue)
            simp [tableInput, tablePayload, hzero, heq]
          · have hchildren : ∀ child,
                child ∈ (Position.chain lay tree leafIdx chainIdx step).children →
                  left (.position child) = right (.position child) := by
              have hleft' : ∀ child,
                  child ∈ (Position.chain lay tree leafIdx chainIdx step).children →
                    state.values (.position child) = some (left (.position child)) := by
                simpa [TableInputAvailable, hzero] using hleft
              have hright' : ∀ child,
                  child ∈ (Position.chain lay tree leafIdx chainIdx step).children →
                    state.values (.position child) = some (right (.position child)) := by
                simpa [TableInputAvailable, hzero] using hright
              intro child hchild
              have hl := hleft' child hchild
              have hr := hright' child hchild
              exact Option.some.inj (hl.symm.trans hr)
            have hmap :
                (Position.chain lay tree leafIdx chainIdx step).children.map
                    (tableValue left) =
                  (Position.chain lay tree leafIdx chainIdx step).children.map
                    (tableValue right) := by
              apply List.map_congr_left
              intro child hchild
              simp only [tableValue, hchildren child hchild]
            simp [tableInput, tablePayload, hzero, hmap]
      | leaf lay tree leafIdx =>
          have hchildren : ∀ child,
              child ∈ (Position.leaf lay tree leafIdx).children →
                left (.position child) = right (.position child) := by
            intro child hchild
            exact Option.some.inj ((hleft child hchild).symm.trans (hright child hchild))
          have hmap :
              (Position.leaf lay tree leafIdx).children.map (tableValue left) =
                (Position.leaf lay tree leafIdx).children.map (tableValue right) := by
            apply List.map_congr_left
            intro child hchild
            simp only [tableValue, hchildren child hchild]
          simp [tableInput, tablePayload, hmap]
      | node lay tree level nodeIdx =>
          have hchildren : ∀ child,
              child ∈ (Position.node lay tree level nodeIdx).children →
                left (.position child) = right (.position child) := by
            intro child hchild
            exact Option.some.inj ((hleft child hchild).symm.trans (hright child hchild))
          have hmap :
              (Position.node lay tree level nodeIdx).children.map (tableValue left) =
                (Position.node lay tree level nodeIdx).children.map (tableValue right) := by
            apply List.map_congr_left
            intro child hchild
            simp only [tableValue, hchildren child hchild]
          simp [tableInput, tablePayload, hmap]
      | ftsLeaf index tree leafIdx =>
          have hchildren : ∀ child,
              child ∈ (Position.ftsLeaf index tree leafIdx).children →
                left (.position child) = right (.position child) := by
            intro child hchild
            exact Option.some.inj ((hleft child hchild).symm.trans (hright child hchild))
          have hmap :
              (Position.ftsLeaf index tree leafIdx).children.map (tableValue left) =
                (Position.ftsLeaf index tree leafIdx).children.map (tableValue right) := by
            apply List.map_congr_left
            intro child hchild
            simp only [tableValue, hchildren child hchild]
          simp [tableInput, tablePayload, hmap]
      | ftsNode index tree level nodeIdx =>
          have hchildren : ∀ child,
              child ∈ (Position.ftsNode index tree level nodeIdx).children →
                left (.position child) = right (.position child) := by
            intro child hchild
            exact Option.some.inj ((hleft child hchild).symm.trans (hright child hchild))
          have hmap :
              (Position.ftsNode index tree level nodeIdx).children.map (tableValue left) =
                (Position.ftsNode index tree level nodeIdx).children.map (tableValue right) := by
            apply List.map_congr_left
            intro child hchild
            simp only [tableValue, hchildren child hchild]
          simp [tableInput, tablePayload, hmap]
      | ftsRoots index =>
          have hchildren : ∀ child,
              child ∈ (Position.ftsRoots index).children →
                left (.position child) = right (.position child) := by
            intro child hchild
            exact Option.some.inj ((hleft child hchild).symm.trans (hright child hchild))
          have hmap :
              (Position.ftsRoots index).children.map (tableValue left) =
                (Position.ftsRoots index).children.map (tableValue right) := by
            apply List.map_congr_left
            intro child hchild
            simp only [tableValue, hchildren child hchild]
          simp [tableInput, tablePayload, hmap]

theorem resolvedChainComputation_run_eq_finalQuery_of_available
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (completion : Coordinate → HashOutput) (context : DeferredContext)
    (cache : QueryCache HashSpec) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
    (input : HashInput)
    (hcompletion : DeferredCompletion table context completion)
    (havailable : TableInputAvailable completion context.state
      (.position (.chain lay tree leafIdx chainIdx step)))
    (hclosed : VisibleResolvedComputationsCached parameter table context cache)
    (hinput : input = tableInput parameter completion
      (.position (.chain lay tree leafIdx chainIdx step))) :
    (simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table
          (.chain lay tree leafIdx chainIdx step))).run cache =
      ((randomOracle input).run cache >>= fun result =>
        pure (truncateHash result.1, result.2)) := by
  by_cases hzero : step.val = 0
  · have hstep : step = ⟨0, by norm_num [chainLength, winternitzBits]⟩ := Fin.ext hzero
    have hstart : truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩) =
        truncateHash (completion (.chainStart lay tree leafIdx chainIdx)) := by
      simpa [OtsSecretIndex.coordinate] using congrArg truncateHash
        (hcompletion.2.2.2 ⟨lay, tree, leafIdx, chainIdx⟩).symm
    have hquery : tweakableHashInput parameter
          (.chain lay tree leafIdx chainIdx step)
          (digestBytes (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) = input := by
      rw [hinput, tableInput, tablePayload, if_pos hzero, Position.domain, hstart]
    have hquery' : tweakableHashInput parameter
          (.chain lay tree leafIdx chainIdx
            ⟨0, by norm_num [chainLength, winternitzBits]⟩)
          (digestBytes (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) = input := by
      simpa only [hstep] using hquery
    rw [resolvedPositionComputation, hstep]
    simp only [chainWalk, Nat.zero_add, pure_bind]
    rw [dif_pos (show 0 < chainLength - 1 by norm_num [chainLength, winternitzBits])]
    simp only [tweakableHash, simulateQ_bind, StateT.run_bind,
      simulateQ_pure, StateT.run_pure]
    rw [hquery']
    have horacle : simulateQ (randomOracle : QueryImpl HashSpec _)
        (oracleHash input) = randomOracle input := by
      simpa only [oracleHash, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
    rw [horacle]
  · have hpositive : 0 < step.val := Nat.pos_of_ne_zero hzero
    let previous : ChainStep := ⟨step.val - 1, by omega⟩
    have hpreviousMem : Position.chain lay tree leafIdx chainIdx previous ∈
        (Position.chain lay tree leafIdx chainIdx step).children := by
      simp [Position.children, hpositive, previous]
    have havailable' : ∀ child,
        child ∈ (Position.chain lay tree leafIdx chainIdx step).children →
          context.state.values (.position child) = some (completion (.position child)) := by
      simpa [TableInputAvailable, hzero] using havailable
    have hpreviousState := havailable'
      (.chain lay tree leafIdx chainIdx previous) hpreviousMem
    have hprevious := hclosed (.chain lay tree leafIdx chainIdx previous)
      (completion (.position (.chain lay tree leafIdx chainIdx previous)))
      (by simp [ResolvableOtsPosition]) hpreviousState
    have hprefixEq : step.val = previous.val + 1 := by
      simp [previous]
      omega
    have hprefixComputation :
        resolvedPositionComputation parameter table
            (.chain lay tree leafIdx chainIdx previous) =
          chainWalk parameter lay tree leafIdx chainIdx 0 step.val
            (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) := by
      simp [resolvedPositionComputation, hprefixEq]
    have hprefixRun := simulateQ_randomOracle_run_eq_pure_of_cachedRun
      (agreesWithFn_fromCache cache) hprevious.1
    rw [hprefixComputation] at hprefixRun
    have hpreviousValue : evalWithAnswerFn (fromCache cache)
          (chainWalk parameter lay tree leafIdx chainIdx 0 step.val
            (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) =
        truncateHash (completion (.position
          (.chain lay tree leafIdx chainIdx previous))) := by
      rw [← hprefixComputation]
      exact hprevious.2
    have hquery : tweakableHashInput parameter
          (.chain lay tree leafIdx chainIdx step)
          (digestBytes (truncateHash (completion (.position
            (.chain lay tree leafIdx chainIdx previous))))) = input := by
      rw [hinput, tableInput, tablePayload, if_neg hzero, Position.domain]
      simp [Position.children, hpositive, previous, tableValue]
    rw [resolvedPositionComputation,
      show step.val + 1 = step.val + 1 by rfl,
      chainWalk_add parameter lay tree leafIdx chainIdx 0 step.val 1]
    rw [simulateQ_bind, StateT.run_bind, hprefixRun]
    simp only [pure_bind]
    rw [hpreviousValue]
    rw [chainWalk]
    rw [chainWalk]
    simp only [Nat.zero_add, Nat.add_zero, pure_bind]
    rw [dif_pos (show step.val < chainLength - 1 by have := step.isLt; omega)]
    simp only [tweakableHash, simulateQ_bind, StateT.run_bind,
      simulateQ_pure, StateT.run_pure]
    have hquery' : tweakableHashInput parameter
          (.chain lay tree leafIdx chainIdx
            ⟨step.val, by have := step.isLt; omega⟩)
          (digestBytes (truncateHash (completion (.position
            (.chain lay tree leafIdx chainIdx previous))))) = input := by
      simpa only [Fin.eta] using hquery
    rw [hquery']
    have horacle : simulateQ (randomOracle : QueryImpl HashSpec _)
        (oracleHash input) = randomOracle input := by
      simpa only [oracleHash, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
    rw [horacle]

theorem resolvedLeafComputation_run_eq_finalQuery_of_available
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (completion : Coordinate → HashOutput) (context : DeferredContext)
    (cache : QueryCache HashSpec) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (input : HashInput)
    (hcompletion : DeferredCompletion table context completion)
    (havailable : TableInputAvailable completion context.state
      (.position (.leaf lay tree leafIdx)))
    (hclosed : VisibleResolvedComputationsCached parameter table context cache)
    (hinput : input = tableInput parameter completion
      (.position (.leaf lay tree leafIdx))) :
    (simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table (.leaf lay tree leafIdx))).run cache =
      ((randomOracle input).run cache >>= fun result =>
        pure (truncateHash result.1, result.2)) := by
  let endpointPosition := fun chainIdx : ChainIndex =>
    Position.chain lay tree leafIdx chainIdx Position.lastChainStep
  have havailable' : ∀ chainIdx,
      context.state.values (.position (endpointPosition chainIdx)) =
        some (completion (.position (endpointPosition chainIdx))) := by
    intro chainIdx
    apply havailable (endpointPosition chainIdx)
    simp [endpointPosition, Position.children]
  have hcomponent : ∀ chainIdx,
      CachedRun cache (fromCache cache)
          (chainWalk parameter lay tree leafIdx chainIdx 0 (chainLength - 1)
            (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) ∧
        evalWithAnswerFn (fromCache cache)
            (chainWalk parameter lay tree leafIdx chainIdx 0 (chainLength - 1)
              (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) =
          truncateHash (completion (.position (endpointPosition chainIdx))) := by
    intro chainIdx
    have hendpoint := hclosed (endpointPosition chainIdx)
      (completion (.position (endpointPosition chainIdx)))
      (by simp [endpointPosition, ResolvableOtsPosition]) (havailable' chainIdx)
    simpa [endpointPosition, resolvedPositionComputation, Position.lastChainStep,
      chainLength, winternitzBits] using hendpoint
  have hpublicCached : CachedRun cache (fromCache cache)
      (oneTimePublicKey parameter lay tree leafIdx
        (fun chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) := by
    unfold oneTimePublicKey
    exact CachedRun.sequenceFin _ fun chainIdx => (hcomponent chainIdx).1
  have hpublicRun := simulateQ_randomOracle_run_eq_pure_of_cachedRun
    (agreesWithFn_fromCache cache) hpublicCached
  have hpublicValue : evalWithAnswerFn (fromCache cache)
        (oneTimePublicKey parameter lay tree leafIdx
          (fun chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))) =
      fun chainIdx => truncateHash (completion (.position (endpointPosition chainIdx))) := by
    rw [eval_oneTimePublicKey]
    funext chainIdx
    exact (hcomponent chainIdx).2
  have hquery : tweakableHashInput parameter (.leaf lay tree leafIdx)
        (leafPayload fun chainIdx =>
          truncateHash (completion (.position (endpointPosition chainIdx)))) = input := by
    have hleafInput := leafInput_eq_tableInput_of_completion parameter table lay tree leafIdx
      context
      (fun chainIdx => truncateHash (completion (.position (endpointPosition chainIdx))))
      (fun chainIdx => by
        refine ⟨completion (.position (endpointPosition chainIdx)), ?_, rfl⟩
        unfold DeferredContext.positionValue
        rw [havailable' chainIdx])
      completion hcompletion
    exact hleafInput.trans hinput.symm
  rw [resolvedPositionComputation, simulateQ_bind, StateT.run_bind, hpublicRun]
  simp only [pure_bind]
  rw [hpublicValue]
  simp only [leafHash, tweakableHash, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure]
  rw [hquery]
  have horacle : simulateQ (randomOracle : QueryImpl HashSpec _)
      (oracleHash input) = randomOracle input := by
    simpa only [oracleHash, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
  rw [horacle]

theorem resolvedPositionComputation_deferredTreePosition
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight) (hnode : nodeIdx < 2 ^ maxLayerHeight) :
    resolvedPositionComputation parameter table
        (deferredTreePosition lay tree level nodeIdx hlevel) =
      treeNode parameter lay tree
        (fun leafIdx chainIdx =>
          truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) level nodeIdx := by
  cases level with
  | zero => simp [deferredTreePosition, resolvedPositionComputation, treeNode_zero_eq]
  | succ current =>
      simp [deferredTreePosition, resolvedPositionComputation, leafOfNat,
        Nat.mod_eq_of_lt hnode]

theorem resolvableOtsPosition_deferredTreePosition
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight)
    (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    ResolvableOtsPosition (deferredTreePosition lay tree level nodeIdx hlevel) := by
  have hnode : nodeIdx < 2 ^ maxLayerHeight := by
    have hpow : 0 < 2 ^ level := pow_pos (by omega) _
    nlinarith
  cases level with
  | zero => simp [deferredTreePosition, ResolvableOtsPosition]
  | succ current =>
      simpa [deferredTreePosition, ResolvableOtsPosition, leafOfNat,
        Nat.mod_eq_of_lt hnode] using hspan

set_option maxRecDepth 100000 in
theorem resolvedNodeComputation_run_eq_finalQuery_of_available
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (completion : Coordinate → HashOutput) (context : DeferredContext)
    (cache : QueryCache HashSpec) (lay : Layer) (tree : TreeIndex)
    (level : Fin maxLayerHeight) (nodeIdx : LeafIndex) (input : HashInput)
    (hcompletion : DeferredCompletion table context completion)
    (hresolvable : ResolvableOtsPosition (.node lay tree level nodeIdx))
    (havailable : TableInputAvailable completion context.state
      (.position (.node lay tree level nodeIdx)))
    (hclosed : VisibleResolvedComputationsCached parameter table context cache)
    (hinput : input = tableInput parameter completion
      (.position (.node lay tree level nodeIdx))) :
    (simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table
          (.node lay tree level nodeIdx))).run cache =
      ((randomOracle input).run cache >>= fun result =>
        pure (truncateHash result.1, result.2)) := by
  let leftPosition := deferredTreePosition lay tree level.val (2 * nodeIdx.val)
    (by have := level.isLt; omega)
  let rightPosition := deferredTreePosition lay tree level.val (2 * nodeIdx.val + 1)
    (by have := level.isLt; omega)
  have hspan : 2 ^ (level.val + 1) * (nodeIdx.val + 1) ≤ 2 ^ maxLayerHeight := by
    simpa [ResolvableOtsPosition] using hresolvable
  have hleftSpan : 2 ^ level.val * (2 * nodeIdx.val + 1) ≤ 2 ^ maxLayerHeight := by
    rw [pow_succ] at hspan
    calc
      2 ^ level.val * (2 * nodeIdx.val + 1) ≤
          2 ^ level.val * (2 * (nodeIdx.val + 1)) := by
        exact Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ level.val * 2 * (nodeIdx.val + 1) := by ring
      _ ≤ 2 ^ maxLayerHeight := hspan
  have hrightSpan : 2 ^ level.val * (2 * nodeIdx.val + 1 + 1) ≤
      2 ^ maxLayerHeight := by
    rw [pow_succ] at hspan
    calc
      2 ^ level.val * (2 * nodeIdx.val + 1 + 1) =
          2 ^ level.val * 2 * (nodeIdx.val + 1) := by ring
      _ ≤ 2 ^ maxLayerHeight := hspan
  have hleftNode : 2 * nodeIdx.val < 2 ^ maxLayerHeight := by
    have hpow : 0 < 2 ^ level.val := pow_pos (by omega) _
    nlinarith
  have hrightNode : 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight := by
    have hpow : 0 < 2 ^ level.val := pow_pos (by omega) _
    nlinarith
  have hchildren : (Position.node lay tree level nodeIdx).children =
      [leftPosition, rightPosition] := by
    dsimp [leftPosition, rightPosition]
    by_cases hzero : level.val = 0
    · have hlevelEq : level = ⟨0, by have := level.isLt; omega⟩ := Fin.ext hzero
      rw [hlevelEq]
      simp [Position.children, deferredTreePosition, hrightNode, leafOfNat,
        Nat.mod_eq_of_lt hleftNode, Nat.mod_eq_of_lt hrightNode]
    · obtain ⟨current, hcurrent⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hlevelEq : level = ⟨current + 1, by have := level.isLt; omega⟩ := Fin.ext hcurrent
      rw [hlevelEq]
      simp [Position.children, deferredTreePosition, hrightNode, leafOfNat,
        Nat.mod_eq_of_lt hleftNode, Nat.mod_eq_of_lt hrightNode]
  have hleftState : context.state.values (.position leftPosition) =
      some (completion (.position leftPosition)) := by
    apply havailable leftPosition
    rw [hchildren]
    simp
  have hrightState : context.state.values (.position rightPosition) =
      some (completion (.position rightPosition)) := by
    apply havailable rightPosition
    rw [hchildren]
    simp
  have hleftResolvable : ResolvableOtsPosition leftPosition := by
    exact resolvableOtsPosition_deferredTreePosition lay tree level.val
      (2 * nodeIdx.val) (by have := level.isLt; omega) hleftSpan
  have hrightResolvable : ResolvableOtsPosition rightPosition := by
    exact resolvableOtsPosition_deferredTreePosition lay tree level.val
      (2 * nodeIdx.val + 1) (by have := level.isLt; omega) hrightSpan
  have hleft := hclosed leftPosition (completion (.position leftPosition))
    hleftResolvable hleftState
  have hright := hclosed rightPosition (completion (.position rightPosition))
    hrightResolvable hrightState
  have hleftComputation := resolvedPositionComputation_deferredTreePosition parameter table
    lay tree level.val (2 * nodeIdx.val) (by have := level.isLt; omega) hleftNode
  have hrightComputation := resolvedPositionComputation_deferredTreePosition parameter table
    lay tree level.val (2 * nodeIdx.val + 1) (by have := level.isLt; omega) hrightNode
  have hleftCached : CachedRun cache (fromCache cache)
      (treeNode parameter lay tree
        (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
        level.val (2 * nodeIdx.val)) := by
    rw [← hleftComputation]
    exact hleft.1
  have hrightCached : CachedRun cache (fromCache cache)
      (treeNode parameter lay tree
        (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
        level.val (2 * nodeIdx.val + 1)) := by
    rw [← hrightComputation]
    exact hright.1
  have hleftRun := simulateQ_randomOracle_run_eq_pure_of_cachedRun
    (agreesWithFn_fromCache cache) hleftCached
  have hrightRun := simulateQ_randomOracle_run_eq_pure_of_cachedRun
    (agreesWithFn_fromCache cache) hrightCached
  have hleftValue : evalWithAnswerFn (fromCache cache)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          level.val (2 * nodeIdx.val)) =
      truncateHash (completion (.position leftPosition)) := by
    rw [← hleftComputation]
    exact hleft.2
  have hrightValue : evalWithAnswerFn (fromCache cache)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          level.val (2 * nodeIdx.val + 1)) =
      truncateHash (completion (.position rightPosition)) := by
    rw [← hrightComputation]
    exact hright.2
  have hleftPositionValue : context.positionValue leftPosition =
      some (completion (.position leftPosition)) := by
    unfold DeferredContext.positionValue
    rw [hleftState]
  have hrightPositionValue : context.positionValue rightPosition =
      some (completion (.position rightPosition)) := by
    unfold DeferredContext.positionValue
    rw [hrightState]
  have hquery : tweakableHashInput parameter
        (.node lay tree (level.val + 1) nodeIdx.val)
        (nodePayload (truncateHash (completion (.position leftPosition)))
          (truncateHash (completion (.position rightPosition)))) = input := by
    have hnodeInput := nodeInput_eq_tableInput_of_completion parameter table lay tree
      level.val nodeIdx.val level.isLt hspan context
      (truncateHash (completion (.position leftPosition)))
      (truncateHash (completion (.position rightPosition)))
      (completion (.position leftPosition)) (completion (.position rightPosition))
      (by simpa [leftPosition] using hleftPositionValue)
      (by simpa [rightPosition] using hrightPositionValue)
      rfl rfl completion hcompletion
    have htarget : Position.node lay tree ⟨level.val, level.isLt⟩
        (leafOfNat nodeIdx.val) = Position.node lay tree level nodeIdx := by
      simp [leafOfNat_val]
    rw [htarget] at hnodeInput
    exact hnodeInput.trans hinput.symm
  rw [resolvedPositionComputation, treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
    hleftRun]
  simp only [pure_bind]
  rw [simulateQ_bind, StateT.run_bind, hrightRun]
  simp only [pure_bind]
  rw [hleftValue, hrightValue]
  simp only [tweakableHash, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure]
  rw [hquery]
  have horacle : simulateQ (randomOracle : QueryImpl HashSpec _)
      (oracleHash input) = randomOracle input := by
    simpa only [oracleHash, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
  rw [horacle]

theorem resolvedPositionComputation_run_eq_finalQuery_of_available
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (completion : Coordinate → HashOutput) (context : DeferredContext)
    (cache : QueryCache HashSpec) (position : Position) (input : HashInput)
    (hcompletion : DeferredCompletion table context completion)
    (hresolvable : ResolvableOtsPosition position)
    (havailable : TableInputAvailable completion context.state (.position position))
    (hclosed : VisibleResolvedComputationsCached parameter table context cache)
    (hinput : input = tableInput parameter completion (.position position)) :
    (simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table position)).run cache =
      ((randomOracle input).run cache >>= fun result =>
        pure (truncateHash result.1, result.2)) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      exact resolvedChainComputation_run_eq_finalQuery_of_available parameter table completion
        context cache lay tree leafIdx chainIdx step input hcompletion havailable hclosed hinput
  | leaf lay tree leafIdx =>
      exact resolvedLeafComputation_run_eq_finalQuery_of_available parameter table completion
        context cache lay tree leafIdx input hcompletion havailable hclosed hinput
  | node lay tree level nodeIdx =>
      exact resolvedNodeComputation_run_eq_finalQuery_of_available parameter table completion
        context cache lay tree level nodeIdx input hcompletion hresolvable havailable hclosed hinput
  | ftsLeaf index tree leafIdx => simp [ResolvableOtsPosition] at hresolvable
  | ftsNode index tree level nodeIdx => simp [ResolvableOtsPosition] at hresolvable
  | ftsRoots index => simp [ResolvableOtsPosition] at hresolvable

noncomputable def resolvedRevealComputation
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (input : HashInput) : OracleComp HashSpec Digest := by
  classical
  exact if ResolvableOtsPosition position then
      resolvedPositionComputation parameter table position
    else
      do
        let output ← oracleHash input
        pure (truncateHash output)

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredPosition_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (context : DeferredContext)
    (ordinaryCache cache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache cache)
    (hresolvable : ResolvableOtsPosition position) :
    RelTriple
      (resolveDeferredPosition table position context)
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table position)).run cache)
      (ResolvePositionRel parameter table ordinaryCache position) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      have hchain := relTriple_resolveDeferredChainPrefix_chronological parameter table lay tree
        leafIdx chainIdx context ordinaryCache cache hinvariant (step.val + 1)
          (by have := step.isLt; omega)
      apply relTriple_post_mono hchain
      intro leftResult rightResult hrelation
      cases leftResult with
      | none => trivial
      | some resolved =>
          rcases rightResult with ⟨value, finalCache⟩
          rcases hrelation with ⟨hvalue, hcontext, htip⟩
          refine ⟨hvalue, hcontext, ?_⟩
          rcases htip with ⟨hzero, _⟩ | ⟨previous, hprevious, hposition⟩
          · have : 0 < step.val + 1 := by omega
            omega
          · have heq : previous = step := by
              apply Fin.ext
              omega
            simpa [heq] using hposition
  | leaf lay tree leafIdx =>
      simpa [resolveDeferredPosition, resolvedPositionComputation] using
        relTriple_resolveDeferredOtsLeaf_chronological parameter table lay tree leafIdx
          context ordinaryCache cache hinvariant
  | node lay tree level nodeIdx =>
      have hnode := relTriple_resolveDeferredTreeNode_chronological parameter table lay tree
        (level.val + 1) nodeIdx.val (by have := level.isLt; omega) hresolvable context
          ordinaryCache cache hinvariant
      simpa [resolveDeferredPosition, resolvedPositionComputation, deferredTreePosition,
        leafOfNat_val] using hnode
  | ftsLeaf index tree leafIdx => simp [ResolvableOtsPosition] at hresolvable
  | ftsNode index tree level nodeIdx => simp [ResolvableOtsPosition] at hresolvable
  | ftsRoots index => simp [ResolvableOtsPosition] at hresolvable

set_option maxRecDepth 100000 in
theorem relTriple_resolveDeferredReveal_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (input : HashInput)
    (context : DeferredContext) (ordinaryCache cache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context ordinaryCache cache)
    (hots : IsOtsPosition position)
    (hcanonical : ∀ completion, DeferredCompletion table context completion →
      input = tableInput parameter completion (.position position)) :
    RelTriple
      (resolveDeferredReveal table position context)
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedRevealComputation parameter table position input)).run cache)
      (ResolvePositionRel parameter table ordinaryCache position) := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · simpa [resolveDeferredReveal, resolvedRevealComputation, hresolvable] using
      relTriple_resolveDeferredPosition_chronological parameter table position context
        ordinaryCache cache hinvariant hresolvable
  · have hdirect := relTriple_resolveDeferredPositionValue_chronological parameter table
      position context ordinaryCache cache input hinvariant hots hcanonical
    simpa [resolveDeferredReveal, resolvedRevealComputation, hresolvable, oracleHash,
      simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure] using hdirect

def ResolvedOrdinaryRunRel (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (alpha × SplitHashCache)) →
      alpha × QueryCache HashSpec → Prop
  | none, _ => True
  | some result, (value, concreteCache) =>
      result.table = table ∧ result.value.1 = value ∧
        ResolvedContextInvariant parameter table result.context
          (ordinaryQueryCache result.value.2) concreteCache

def DoomedResolvedContext (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) : Prop :=
  context.ValuesConsistent ∧ StartTableAgrees context.state table ∧
    ¬DeferredCompletable table context

def ResolvedRunRel (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (alpha × SplitHashCache)) →
      alpha × QueryCache HashSpec → Prop
  | none, _ => True
  | some result, (value, concreteCache) =>
      (result.table = table ∧ result.value.1 = value ∧
        ResolvedContextInvariant parameter table result.context
          (ordinaryQueryCache result.value.2) concreteCache) ∨
      (result.table = table ∧ DoomedResolvedContext table result.context)

theorem relTriple_runResolvedFromTable_publishOrdinaryInput
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (input : HashInput) (output : HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hconcrete : concreteCache input = some output) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((publishOrdinaryInput coordinate input output).run cache))
      (pure (output, concreteCache) : ProbComp (HashOutput × QueryCache HashSpec))
      (ResolvedRunRel parameter table) := by
  obtain ⟨publishedContext, hpublish, hpublishedInvariant⟩ :=
    (resolvedAdministrative_publishCoordinate coordinate).run_preserves_invariant
      context cache fuel concreteCache hinvariant
  unfold publishOrdinaryInput
  rw [StateT.run_bind, runResolvedFromTable_bind, hpublish]
  simp only [StateT.run_pure, runResolvedFromTable]
  apply relTriple_pure_pure
  refine Or.inl ⟨rfl, rfl, ?_⟩
  rw [ordinaryQueryCache_update]
  exact hpublishedInvariant.cacheLeft_of_concrete input output hconcrete

theorem relTriple_runResolvedFromTable_splitHashQuery_completionOrdinary
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (context : DeferredContext)
    (hordinary : CompletionOrdinaryInput parameter table context input)
    (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((splitHashQuery (.ordinary input)).run cache))
      ((randomOracle input).run concreteCache)
      (ResolvedOrdinaryRunRel parameter table) := by
  have hcacheEq := hinvariant.2.2.2.2.eq_of_completionOrdinary
    hinvariant.2.2.2.1 input hordinary
  rw [splitHashQuery_run_eq]
  cases hlookup : cache (.ordinary input) with
  | some output =>
      have hordinaryCached : ordinaryQueryCache cache input = some output := hlookup
      have hconcrete : concreteCache input = some output := by
        rw [← hcacheEq]
        exact hordinaryCached
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hconcrete]
      simp [runResolvedFromTable, ResolvedOrdinaryRunRel]
      exact hinvariant
  | none =>
      have hordinaryCached : ordinaryQueryCache cache input = none := hlookup
      have hconcrete : concreteCache input = none := by
        rw [← hcacheEq]
        exact hordinaryCached
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hconcrete,
        LazyRevealProbe.hashOutputQuery,
        runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput heq
      subst rightOutput
      apply relTriple_pure_pure
      refine ⟨rfl, rfl, ?_⟩
      rw [ordinaryQueryCache_update]
      exact hinvariant.of_completionOrdinary_cacheQuery input leftOutput hordinary

theorem relTriple_runResolvedFromTable_splitHashQuery_stable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((splitHashQuery (.ordinary input)).run cache))
      ((randomOracle input).run concreteCache)
      (ResolvedOrdinaryRunRel parameter table) := by
  exact relTriple_runResolvedFromTable_splitHashQuery_completionOrdinary parameter table input
    context (completionOrdinaryInput_of_stable hstable) fuel cache concreteCache hinvariant

def ResolvedStructuralRunRel (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (Digest × SplitHashCache)) →
      Digest × QueryCache HashSpec → Prop
  | none, _ => True
  | some result, (value, concreteCache) =>
      result.table = table ∧ result.value.1 = value ∧
        (ResolvedContextInvariant parameter table result.context
            (ordinaryQueryCache result.value.2) concreteCache ∨
          DoomedResolvedContext table result.context)

theorem ResolvedOrdinaryRunRel.to_resolvedRunRel
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (alpha × SplitHashCache))}
    {right : alpha × QueryCache HashSpec}
    (hrelation : ResolvedOrdinaryRunRel parameter table left right) :
    ResolvedRunRel parameter table left right := by
  cases left with
  | none => trivial
  | some result => exact Or.inl hrelation

theorem ResolvedStructuralRunRel.to_resolvedRunRel
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (Digest × SplitHashCache))}
    {right : Digest × QueryCache HashSpec}
    (hrelation : ResolvedStructuralRunRel parameter table left right) :
    ResolvedRunRel parameter table left right := by
  cases left with
  | none => trivial
  | some result =>
      rcases hrelation with ⟨htable, hvalue, hinvariant | hdoomed⟩
      · exact Or.inl ⟨htable, hvalue, hinvariant⟩
      · exact Or.inr ⟨htable, hdoomed⟩

theorem relTriple_runResolvedFromTable_of_doomed
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (right : ProbComp (alpha × QueryCache HashSpec))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hdoomed : DoomedResolvedContext table context) :
    RelTriple
      (runResolvedFromTable context fuel table (computation.run cache))
      right (ResolvedRunRel parameter table) := by
  have hbase := relTriple_true
    (runResolvedFromTable context fuel table (computation.run cache)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (runResolvedFromTable context fuel table (computation.run cache)))
      (fun result hresult => hresult)
  apply relTriple_post_mono hsupported
  intro leftResult _ hrelation
  rcases hrelation with ⟨_true, hsupport⟩
  cases leftResult with
  | none => trivial
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable (computation.run cache) context fuel
        table result hdoomed.1 hdoomed.2.1 hsupport
      have hstillDoomed := not_deferredCompletable_of_mem_runResolvedFromTable
        (computation.run cache) context fuel table result hdoomed.1 hdoomed.2.1 hsupport
          hdoomed.2.2
      exact Or.inr ⟨hcore.1, hcore.2.1, hcore.2.2, hstillDoomed⟩

theorem relTriple_runResolvedFromTable_bind_clean_or_doomed
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (next : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta)
    (right : ProbComp (alpha × QueryCache HashSpec))
    (rightNext : alpha → QueryCache HashSpec →
      ProbComp (beta × QueryCache HashSpec))
    (hleft : RelTriple
      (runResolvedFromTable context fuel table (left.run cache))
      right (ResolvedRunRel parameter table))
    (hnext : ∀ (result : ResolvedRunResult (alpha × SplitHashCache))
      (value : alpha) (concreteCache : QueryCache HashSpec),
      result.table = table → result.value.1 = value →
      ResolvedContextInvariant parameter table result.context
        (ordinaryQueryCache result.value.2) concreteCache →
      RelTriple
        (runResolvedFromTable result.context result.remaining result.table
          ((next result.value.1).run result.value.2))
        (rightNext value concreteCache)
        (ResolvedRunRel parameter table)) :
    RelTriple
      (runResolvedFromTable context fuel table ((left >>= next).run cache))
      (right >>= fun result => rightNext result.1 result.2)
      (ResolvedRunRel parameter table) := by
  rw [StateT.run_bind, runResolvedFromTable_bind]
  apply relTriple_bind hleft
  intro leftResult rightResult hrelation
  cases leftResult with
  | none =>
      have hbase := relTriple_true
        (pure (none : Option (ResolvedRunResult (beta × SplitHashCache))) :
          ProbComp (Option (ResolvedRunResult (beta × SplitHashCache))))
        (rightNext rightResult.1 rightResult.2)
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
      · exact hnext result rightResult.1 rightResult.2 hclean.1 hclean.2.1 hclean.2.2
      · simpa [hdoomed.1] using
          (relTriple_runResolvedFromTable_of_doomed parameter table
            (next result.value.1) (rightNext rightResult.1 rightResult.2) result.context
              result.remaining result.value.2 hdoomed.2)

def ResolvedCouples (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (right : StateT (QueryCache HashSpec) ProbComp alpha) : Prop :=
  ∀ context fuel cache concreteCache,
    ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache →
    RelTriple
      (runResolvedFromTable context fuel table (left.run cache))
      (right.run concreteCache)
      (ResolvedRunRel parameter table)

theorem resolvedCouples_pure (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (value : alpha) :
    ResolvedCouples parameter table
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
      (pure value : StateT (QueryCache HashSpec) ProbComp alpha) := by
  intro context fuel cache concreteCache hinvariant
  simp only [runResolvedFromTable]
  apply relTriple_pure_pure
  exact Or.inl ⟨rfl, rfl, hinvariant⟩

theorem resolvedCouples_of_administrative
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {value : alpha} (hadministrative : ResolvedAdministrative computation value) :
    ResolvedCouples parameter table computation
      (pure value : StateT (QueryCache HashSpec) ProbComp alpha) := by
  intro context fuel cache concreteCache hinvariant
  obtain ⟨finalContext, hrun, hfinalInvariant⟩ :=
    hadministrative.run_preserves_invariant context cache fuel concreteCache hinvariant
  rw [hrun]
  simp only [StateT.run_pure]
  apply relTriple_pure_pure
  exact Or.inl ⟨rfl, rfl, hfinalInvariant⟩

theorem resolvedCouples_probe
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (candidate : Probe) :
    ResolvedCouples parameter table (probe candidate)
      (pure () : StateT (QueryCache HashSpec) ProbComp Unit) := by
  intro context fuel cache concreteCache hinvariant
  unfold probe
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedFromTable_probe_query_bind]
  cases fuel with
  | zero =>
      simp only [StateT.run_pure]
      apply relTriple_pure_pure
      trivial
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simp only [hrevealed, ↓reduceIte, StateT.run_pure, runResolvedFromTable]
        apply relTriple_pure_pure
        exact Or.inl ⟨rfl, rfl, hinvariant⟩
      · simp only [hrevealed, ↓reduceIte, StateT.run_pure, runResolvedFromTable]
        by_cases hcompletable : DeferredCompletable table
            { context with state :=
                (context.state.addPending candidate.coordinate candidate.candidate) }
        · apply relTriple_pure_pure
          exact Or.inl ⟨rfl, rfl,
            hinvariant.addPending_of_completable candidate.coordinate candidate.candidate
              hcompletable⟩
        · apply relTriple_pure_pure
          exact Or.inr ⟨rfl, hinvariant.2.1.valuesConsistent.addPending
            candidate.coordinate candidate.candidate,
            hinvariant.2.2.1.addPending candidate.coordinate candidate.candidate,
            hcompletable⟩

theorem resolvedCouples_splitUniform
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (n : Nat) :
    ResolvedCouples parameter table (splitUniformImpl n) (unifFwdImpl HashSpec n) := by
  intro context fuel cache concreteCache hinvariant
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, runResolvedFromTable_uniform_query_bind]
  rw [show (unifFwdImpl HashSpec n).run concreteCache =
      (fun output => (output, concreteCache)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) by
    simpa using unifFwdImpl.simulateQ_run
      (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) concreteCache]
  simp only [map_eq_bind_pure_comp]
  apply relTriple_bind (relTriple_refl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro left right heq
  subst right
  simp only [runResolvedFromTable]
  apply relTriple_pure_pure
  exact Or.inl ⟨rfl, rfl, hinvariant⟩

theorem ResolvedCouples.bind
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {right : StateT (QueryCache HashSpec) ProbComp alpha}
    {leftNext : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    {rightNext : alpha → StateT (QueryCache HashSpec) ProbComp beta}
    (hleft : ResolvedCouples parameter table left right)
    (hnext : ∀ value, ResolvedCouples parameter table (leftNext value) (rightNext value)) :
    ResolvedCouples parameter table (left >>= leftNext) (right >>= rightNext) := by
  intro context fuel cache concreteCache hinvariant
  rw [StateT.run_bind]
  apply relTriple_runResolvedFromTable_bind_clean_or_doomed parameter table context fuel cache
    left leftNext (right.run concreteCache) (fun value cache => (rightNext value).run cache)
    (hleft context fuel cache concreteCache hinvariant)
  intro result value finalCache htable hvalue hresultInvariant
  subst value
  simpa [htable] using
    (hnext result.value.1 result.context result.remaining result.value.2 finalCache
      hresultInvariant)

theorem resolvedCouples_sequenceFin
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput} {n : Nat}
    (left : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (right : Fin n → StateT (QueryCache HashSpec) ProbComp alpha)
    (hcomponent : ∀ index, ResolvedCouples parameter table (left index) (right index)) :
    ResolvedCouples parameter table (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using
        (resolvedCouples_pure parameter table Fin.elim0 :
          ResolvedCouples parameter table
            (pure Fin.elim0 : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) (Fin 0 → alpha))
            (pure Fin.elim0 : StateT (QueryCache HashSpec) ProbComp (Fin 0 → alpha)))
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      apply (hcomponent 0).bind
      intro head
      apply (ih (fun index : Fin n => left index.succ)
        (fun index : Fin n => right index.succ)
        (fun index => hcomponent index.succ)).bind
      intro tail
      let assembled : Fin (n + 1) → alpha := Fin.cases head tail
      exact resolvedCouples_pure parameter table assembled

theorem resolvedCouples_simulateQ
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {spec : OracleSpec ι}
    (left : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (right : QueryImpl spec (StateT (QueryCache HashSpec) ProbComp))
    (hquery : ∀ query, ResolvedCouples parameter table (left query) (right query))
    (computation : OracleComp spec alpha) :
    ResolvedCouples parameter table (simulateQ left computation)
      (simulateQ right computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact resolvedCouples_pure parameter table value
  | query_bind query next ih =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      exact (hquery query).bind fun output => ih output

def ReachableResolvedRunRel (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) :
    Option (ResolvedRunResult (alpha × SplitHashCache)) →
      alpha × QueryCache HashSpec → Prop
  | none, _ => True
  | some result, (value, concreteCache) =>
      (result.table = table ∧ result.value.1 = value ∧
        ResolvedContextInvariant parameter table result.context
          (ordinaryQueryCache result.value.2) concreteCache ∧
        VisibleResolvedComputationsCached parameter table result.context concreteCache ∧
        PublishedValues result.context.state) ∨
      (result.table = table ∧ DoomedResolvedContext table result.context)

theorem ReachableResolvedRunRel.to_resolvedRunRel
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : Option (ResolvedRunResult (alpha × SplitHashCache))}
    {right : alpha × QueryCache HashSpec}
    (hrelation : ReachableResolvedRunRel parameter table left right) :
    ResolvedRunRel parameter table left right := by
  cases left with
  | none => trivial
  | some result =>
      rcases hrelation with hclean | hdoomed
      · exact Or.inl ⟨hclean.1, hclean.2.1, hclean.2.2.1⟩
      · exact Or.inr hdoomed

def ReachableResolvedCouples (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (right : StateT (QueryCache HashSpec) ProbComp alpha) : Prop :=
  ∀ context fuel cache concreteCache,
    ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache →
    VisibleResolvedComputationsCached parameter table context concreteCache →
    PublishedValues context.state →
    RelTriple
      (runResolvedFromTable context fuel table (left.run cache))
      (right.run concreteCache)
      (ReachableResolvedRunRel parameter table)

theorem reachableResolvedCouples_pure (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (value : alpha) :
    ReachableResolvedCouples parameter table
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
      (pure value : StateT (QueryCache HashSpec) ProbComp alpha) := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  simp only [runResolvedFromTable]
  apply relTriple_pure_pure
  exact Or.inl ⟨rfl, rfl, hinvariant, hclosed, hpublished⟩

theorem reachableResolvedCouples_of_administrative
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {value : alpha} (hadministrative : ResolvedAdministrative computation value)
    (hpreserves : ResolvedPreservesPublished computation) :
    ReachableResolvedCouples parameter table computation
      (pure value : StateT (QueryCache HashSpec) ProbComp alpha) := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  obtain ⟨finalContext, hrun, hpending, hvalues, hprivate⟩ :=
    hadministrative.run context cache fuel table
  have hcore : context.CoreEq finalContext :=
    ⟨hpending.symm, hvalues.symm, hprivate.symm⟩
  rw [hrun]
  simp only [StateT.run_pure]
  apply relTriple_pure_pure
  refine Or.inl ⟨rfl, rfl, hinvariant.of_coreEq hcore,
    hclosed.of_state_values_eq hvalues, ?_⟩
  apply hpreserves context cache fuel table
    { context := finalContext, remaining := fuel, value := (value, cache), table := table }
    hpublished
  rw [hrun]
  simp

theorem reachableResolvedCouples_probe
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (candidate : Probe) :
    ReachableResolvedCouples parameter table (probe candidate)
      (pure () : StateT (QueryCache HashSpec) ProbComp Unit) := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  unfold probe
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedFromTable_probe_query_bind]
  cases fuel with
  | zero =>
      simp only [StateT.run_pure]
      apply relTriple_pure_pure
      trivial
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simp only [hrevealed, ↓reduceIte, StateT.run_pure, runResolvedFromTable]
        apply relTriple_pure_pure
        exact Or.inl ⟨rfl, rfl, hinvariant, hclosed, hpublished⟩
      · simp only [hrevealed, ↓reduceIte, StateT.run_pure, runResolvedFromTable]
        by_cases hcompletable : DeferredCompletable table
            { context with state :=
                context.state.addPending candidate.coordinate candidate.candidate }
        · apply relTriple_pure_pure
          exact Or.inl ⟨rfl, rfl,
            hinvariant.addPending_of_completable candidate.coordinate candidate.candidate
              hcompletable,
            hclosed.of_state_values_eq rfl, by
              simpa [PublishedValues, LazyRevealProbe.State.addPending] using hpublished⟩
        · apply relTriple_pure_pure
          exact Or.inr ⟨rfl, hinvariant.2.1.valuesConsistent.addPending
            candidate.coordinate candidate.candidate,
            hinvariant.2.2.1.addPending candidate.coordinate candidate.candidate,
            hcompletable⟩

theorem relTriple_runResolvedFromTable_publishCoordinate_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hvalue : context.state.values coordinate ≠ none) :
    RelTriple
      (runResolvedFromTable context fuel table ((publishCoordinate coordinate).run cache))
      (pure ((), concreteCache) : ProbComp (Unit × QueryCache HashSpec))
      (ReachableResolvedRunRel parameter table) := by
  unfold publishCoordinate
  rw [StateT.run_liftM, LazyRevealProbe.publishQuery,
    runResolvedFromTable_publish_query_bind]
  simp only [runResolvedFromTable]
  apply relTriple_pure_pure
  refine Or.inl ⟨rfl, rfl, hinvariant, hclosed.of_state_values_eq rfl, ?_⟩
  intro other hrevealed
  simp only [LazyRevealProbe.State.publish, Finset.mem_insert] at hrevealed
  rcases hrevealed with heq | hrevealed
  · subst other
    exact hvalue
  · exact hpublished other hrevealed

theorem reachableResolvedCouples_splitUniform
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (n : Nat) :
    ReachableResolvedCouples parameter table (splitUniformImpl n)
      (unifFwdImpl HashSpec n) := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, runResolvedFromTable_uniform_query_bind]
  rw [show (unifFwdImpl HashSpec n).run concreteCache =
      (fun output => (output, concreteCache)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) by
    simpa using unifFwdImpl.simulateQ_run
      (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) concreteCache]
  simp only [map_eq_bind_pure_comp]
  apply relTriple_bind (relTriple_refl
    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro left right heq
  subst right
  simp only [runResolvedFromTable]
  apply relTriple_pure_pure
  exact Or.inl ⟨rfl, rfl, hinvariant, hclosed, hpublished⟩

theorem relTriple_runResolvedFromTable_of_doomed_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (right : ProbComp (alpha × QueryCache HashSpec))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hdoomed : DoomedResolvedContext table context) :
    RelTriple
      (runResolvedFromTable context fuel table (computation.run cache))
      right (ReachableResolvedRunRel parameter table) := by
  have hbase := relTriple_true
    (runResolvedFromTable context fuel table (computation.run cache)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (runResolvedFromTable context fuel table (computation.run cache)))
      (fun result hresult => hresult)
  apply relTriple_post_mono hsupported
  intro leftResult _ hrelation
  rcases hrelation with ⟨_true, hsupport⟩
  cases leftResult with
  | none => trivial
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable (computation.run cache) context fuel
        table result hdoomed.1 hdoomed.2.1 hsupport
      have hstillDoomed := not_deferredCompletable_of_mem_runResolvedFromTable
        (computation.run cache) context fuel table result hdoomed.1 hdoomed.2.1 hsupport
          hdoomed.2.2
      exact Or.inr ⟨hcore.1, hcore.2.1, hcore.2.2, hstillDoomed⟩

theorem ReachableResolvedCouples.bind
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {right : StateT (QueryCache HashSpec) ProbComp alpha}
    {leftNext : alpha → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) beta}
    {rightNext : alpha → StateT (QueryCache HashSpec) ProbComp beta}
    (hleft : ReachableResolvedCouples parameter table left right)
    (hnext : ∀ value,
      ReachableResolvedCouples parameter table (leftNext value) (rightNext value)) :
    ReachableResolvedCouples parameter table (left >>= leftNext) (right >>= rightNext) := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  rw [StateT.run_bind, StateT.run_bind, runResolvedFromTable_bind]
  apply relTriple_bind (hleft context fuel cache concreteCache hinvariant hclosed hpublished)
  intro leftResult rightResult hrelation
  cases leftResult with
  | none =>
      have hbase := relTriple_true
        (pure (none : Option (ResolvedRunResult (beta × SplitHashCache))) :
          ProbComp (Option (ResolvedRunResult (beta × SplitHashCache))))
        ((rightNext rightResult.1).run rightResult.2)
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
        simpa [hclean.1] using
          (hnext result.value.1 result.context result.remaining result.value.2 rightCache
            hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2)
      · simpa [hdoomed.1] using
          (relTriple_runResolvedFromTable_of_doomed_reachable parameter table
            (leftNext result.value.1) ((rightNext rightResult.1).run rightResult.2)
              result.context result.remaining result.value.2 hdoomed.2)

theorem ReachableResolvedCouples.publishAfter
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha}
    {right : StateT (QueryCache HashSpec) ProbComp alpha}
    (hleft : ReachableResolvedCouples parameter table left right)
    (coordinate : Coordinate)
    (hmaterialized : ∀ context fuel cache result,
      some result ∈ support
        (runResolvedFromTable context fuel table (left.run cache)) →
      result.context.state.values coordinate ≠ none) :
    ReachableResolvedCouples parameter table
      (left >>= fun value => publishCoordinate coordinate >>= fun _ => pure value) right := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  rw [StateT.run_bind, runResolvedFromTable_bind]
  have hbase := hleft context fuel cache concreteCache hinvariant hclosed hpublished
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (runResolvedFromTable context fuel table (left.run cache)))
      (fun result hresult => hresult)
  rw [show right.run concreteCache = right.run concreteCache >>= fun result => pure result by simp]
  apply relTriple_bind hsupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨hrelation, hleftSupport⟩
  cases leftResult with
  | none =>
      apply relTriple_pure_pure
      trivial
  | some result =>
      rcases hrelation with hclean | hdoomed
      · have hpublish := relTriple_runResolvedFromTable_publishCoordinate_reachable
          parameter table coordinate result.context result.remaining result.value.2 rightResult.2
            hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
              (hmaterialized context fuel cache result hleftSupport)
        simp only
        rw [hclean.1, StateT.run_bind, runResolvedFromTable_bind]
        rw [show (pure rightResult : ProbComp (alpha × QueryCache HashSpec)) =
            (pure ((), rightResult.2) >>= fun _ => pure rightResult) by simp]
        have hpublishSupported :=
          SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hpublish
        apply relTriple_bind hpublishSupported
        intro publishedResult publishedRight hpublishedRelation
        rcases hpublishedRelation with ⟨hpublishedRelation, hrightSupport⟩
        have hpublishedRight : publishedRight = ((), rightResult.2) := by
          simpa using hrightSupport
        subst publishedRight
        cases publishedResult with
        | none =>
            apply relTriple_pure_pure
            trivial
        | some publishedResult =>
            rcases hpublishedRelation with hpublishedClean | hpublishedDoomed
            · simp only [runResolvedFromTable]
              apply relTriple_pure_pure
              exact Or.inl ⟨hpublishedClean.1, hclean.2.1, hpublishedClean.2.2.1,
                hpublishedClean.2.2.2.1, hpublishedClean.2.2.2.2⟩
            · simp only [runResolvedFromTable]
              apply relTriple_pure_pure
              exact Or.inr hpublishedDoomed
      · simpa [hdoomed.1] using
          (relTriple_runResolvedFromTable_of_doomed_reachable parameter table
            (publishCoordinate coordinate >>= fun _ => pure result.value.1)
              (pure rightResult) result.context result.remaining result.value.2 hdoomed.2)

theorem reachableResolvedCouples_sequenceFin
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput} {n : Nat}
    (left : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) alpha)
    (right : Fin n → StateT (QueryCache HashSpec) ProbComp alpha)
    (hcomponent : ∀ index,
      ReachableResolvedCouples parameter table (left index) (right index)) :
    ReachableResolvedCouples parameter table (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simpa [sequenceFin] using
        (reachableResolvedCouples_pure parameter table Fin.elim0 :
          ReachableResolvedCouples parameter table
            (pure Fin.elim0 : StateT SplitHashCache
              (OracleComp (LazyRevealProbe.World Coordinate)) (Fin 0 → alpha))
            (pure Fin.elim0 : StateT (QueryCache HashSpec) ProbComp (Fin 0 → alpha)))
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      apply (hcomponent 0).bind
      intro head
      apply (ih (fun index : Fin n => left index.succ)
        (fun index : Fin n => right index.succ)
        (fun index => hcomponent index.succ)).bind
      intro tail
      let assembled : Fin (n + 1) → alpha := Fin.cases head tail
      exact reachableResolvedCouples_pure parameter table assembled

theorem reachableResolvedCouples_simulateQ
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {spec : OracleSpec ι}
    (left : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (right : QueryImpl spec (StateT (QueryCache HashSpec) ProbComp))
    (hquery : ∀ query,
      ReachableResolvedCouples parameter table (left query) (right query))
    (computation : OracleComp spec alpha) :
    ReachableResolvedCouples parameter table (simulateQ left computation)
      (simulateQ right computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact reachableResolvedCouples_pure parameter table value
  | query_bind query next ih =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      exact (hquery query).bind fun output => ih output

theorem relTriple_runResolvedFromTable_splitHashQuery_completionOrdinary_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (context : DeferredContext)
    (hordinary : CompletionOrdinaryInput parameter table context input)
    (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((splitHashQuery (.ordinary input)).run cache))
      ((randomOracle input).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  have hcacheEq := hinvariant.2.2.2.2.eq_of_completionOrdinary
    hinvariant.2.2.2.1 input hordinary
  rw [splitHashQuery_run_eq]
  cases hlookup : cache (.ordinary input) with
  | some output =>
      have hordinaryCached : ordinaryQueryCache cache input = some output := hlookup
      have hconcrete : concreteCache input = some output := by
        rw [← hcacheEq]
        exact hordinaryCached
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hconcrete]
      simp [runResolvedFromTable, ReachableResolvedRunRel]
      exact Or.inl ⟨hinvariant, hclosed, hpublished⟩
  | none =>
      have hordinaryCached : ordinaryQueryCache cache input = none := hlookup
      have hconcrete : concreteCache input = none := by
        rw [← hcacheEq]
        exact hordinaryCached
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hconcrete,
        LazyRevealProbe.hashOutputQuery,
        runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput heq
      subst rightOutput
      apply relTriple_pure_pure
      refine Or.inl ⟨rfl, rfl, ?_, ?_⟩
      · rw [ordinaryQueryCache_update]
        exact hinvariant.of_completionOrdinary_cacheQuery input leftOutput hordinary
      · exact ⟨hclosed.mono (le_cacheQuery hconcrete), hpublished⟩

theorem reachableResolvedCouples_splitHashQuery_stable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ReachableResolvedCouples parameter table (splitHashQuery (.ordinary input))
      (randomOracle input) := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  exact relTriple_runResolvedFromTable_splitHashQuery_completionOrdinary_reachable parameter
    table input context (completionOrdinaryInput_of_stable hstable) fuel cache concreteCache
      hinvariant hclosed hpublished

theorem reachableResolvedCouples_probingHashQuery_of_stable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ReachableResolvedCouples parameter table (probingHashQuery parameter input)
      (randomOracle input) := by
  rw [probingHashQuery_eq_splitHashQuery_of_stable parameter input hstable]
  exact reachableResolvedCouples_splitHashQuery_stable parameter table input hstable

theorem reachableResolvedCouples_verifierHashQuery_of_stable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ReachableResolvedCouples parameter table (verifierHashQuery parameter input)
      (randomOracle input) := by
  rw [verifierHashQuery_eq_splitHashQuery_of_stable parameter input hstable]
  exact reachableResolvedCouples_splitHashQuery_stable parameter table input hstable

theorem reachableResolvedCouples_revealChainStart
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) :
    ReachableResolvedCouples parameter table
      (revealChainStart index.lay index.tree index.leafIdx index.chainIdx)
      (pure (truncateHash (table index)) : StateT (QueryCache HashSpec) ProbComp Digest) := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  have hclean := hinvariant.2.2.2.1.not_hitAt_chainStart index
  rw [runResolvedFromTable_revealChainStart_of_agrees context fuel table index cache
    hinvariant.2.2.1 hclean]
  apply relTriple_pure_pure
  refine Or.inl ⟨rfl, rfl, ?_, ?_, ?_⟩
  · rw [ordinaryQueryCache_update_hidden]
    exact hinvariant.materialize_chainStart index
  · apply hclosed.of_position_values_eq
    intro position
    have hne : index.coordinate ≠ .position position := by
      rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
      simp [OtsSecretIndex.coordinate]
    simp only [LazyRevealProbe.State.materialize]
    rw [Function.update_of_ne (Ne.symm hne)]
  · exact hpublished.materialize index.coordinate (table index)

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_revealResolvablePosition_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hresolvable : ResolvableOtsPosition position) :
    RelTriple
      (runResolvedFromTable context fuel table ((revealPosition position).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table position)).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  rw [runResolvedFromTable_revealPosition]
  have hresolve := relTriple_resolveDeferredPosition_chronological parameter table position
    context (ordinaryQueryCache cache) concreteCache hinvariant hresolvable
  have hsupportedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolve
      (fun resolved => resolved ∈ support (resolveDeferredPosition table position context))
      (fun resolved hresolved => hresolved)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hsupportedLeft
  have hbound : RelTriple
      (resolveDeferredPosition table position context >>= fun resolved =>
        match resolved with
        | none => pure none
        | some resolved =>
            pure (some ⟨materializeResolvedPosition context position resolved, fuel,
              (truncateHash resolved.output,
                Function.update cache (.hidden (.position position)) (some resolved.output)),
              table⟩))
      (((simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table position)).run concreteCache) >>=
          fun result => pure result)
      (ReachableResolvedRunRel parameter table) := by
    apply relTriple_bind hsupported
    intro resolved rightResult hrelation
    rcases hrelation with ⟨⟨hresolvedRel, hresultSupport⟩, hrightSupport⟩
    cases resolved with
    | none =>
        apply relTriple_pure_pure
        trivial
    | some resolved =>
        apply relTriple_pure_pure
        rcases rightResult with ⟨value, finalCache⟩
        rcases hresolvedRel with ⟨hvalue, hresultInvariant, _hposition⟩
        have hreplay := replay_of_mem_support
          (resolvedPositionComputation parameter table position) concreteCache value finalCache
            hrightSupport (fromCache finalCache) (agreesWithFn_fromCache finalCache)
        have hclosedFinal := hclosed.mono hreplay.1
        have hvisible : VisibleResolvedComputationsCached parameter table
            (materializeResolvedPosition context position resolved) finalCache := by
          intro other output hotherResolvable hvisibleValue
          by_cases heq : other = position
          · subst other
            have houtput : output = resolved.output := by
              have houtput' : resolved.output = output := by
                simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize] using
                  hvisibleValue
              exact houtput'.symm
            subst output
            exact ⟨hreplay.2.2, hreplay.2.1.trans hvalue⟩
          · apply hclosedFinal other output hotherResolvable
            simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize, heq] using
              hvisibleValue
        simp only [ReachableResolvedRunRel]
        rw [ordinaryQueryCache_update_hidden]
        by_cases hcompletable : DeferredCompletable table
            (materializeResolvedPosition context position resolved)
        · have hfinalInvariant := hinvariant.materialize_resolvedReveal position resolved
            (by simpa [resolveDeferredReveal, hresolvable] using hresultSupport)
            hresultInvariant hcompletable
          exact Or.inl (by
            simpa [hvalue] using And.intro hfinalInvariant
              (And.intro hvisible (by
                simpa [materializeResolvedPosition] using
                  hpublished.materialize (.position position) resolved.output)))
        · have hfinalDoomed : DoomedResolvedContext table
              (materializeResolvedPosition context position resolved) := ⟨
            hinvariant.2.1.valuesConsistent.materializeResolvedPosition_of table position
              resolved (by simpa [resolveDeferredReveal, hresolvable] using hresultSupport),
            by simpa [materializeResolvedPosition] using
              hinvariant.2.2.1.materialize_position position resolved.output,
            hcompletable⟩
          exact Or.inr (by simpa using hfinalDoomed)
  simpa [resolveDeferredReveal, hresolvable, materializeResolvedPosition] using hbound

theorem reachableResolvedCouples_revealResolvablePosition
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (hresolvable : ResolvableOtsPosition position) :
    ReachableResolvedCouples parameter table (revealPosition position)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table position)) := by
  intro context fuel cache concreteCache hinvariant hclosed hpublished
  exact relTriple_runResolvedFromTable_revealResolvablePosition_reachable parameter table
    position context fuel cache concreteCache hinvariant hclosed hpublished hresolvable

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_revealPosition_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hots : IsOtsPosition position)
    (hcanonical : ∀ completion, DeferredCompletion table context completion →
      input = tableInput parameter completion (.position position)) :
    RelTriple
      (runResolvedFromTable context fuel table ((revealPosition position).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedRevealComputation parameter table position input)).run concreteCache)
      (ResolvedStructuralRunRel parameter table) := by
  rw [runResolvedFromTable_revealPosition]
  have hresolve := relTriple_resolveDeferredReveal_chronological parameter table position input
    context (ordinaryQueryCache cache) concreteCache hinvariant hots hcanonical
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolve
      (fun resolved => resolved ∈ support (resolveDeferredReveal table position context))
      (fun resolved hresolved => hresolved)
  have hbound : RelTriple
      (resolveDeferredReveal table position context >>= fun resolved =>
        match resolved with
        | none => pure none
        | some resolved =>
            pure (some ⟨materializeResolvedPosition context position resolved, fuel,
              (truncateHash resolved.output,
                Function.update cache (.hidden (.position position)) (some resolved.output)),
              table⟩))
      (((simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedRevealComputation parameter table position input)).run concreteCache) >>=
          fun result => pure result)
      (ResolvedStructuralRunRel parameter table) := by
    apply relTriple_bind hsupported
    intro resolved rightResult hrelation
    rcases hrelation with ⟨hresolvedRel, hresultSupport⟩
    cases resolved with
    | none =>
        apply relTriple_pure_pure
        trivial
    | some resolved =>
        apply relTriple_pure_pure
        rcases rightResult with ⟨value, finalCache⟩
        rcases hresolvedRel with ⟨hvalue, hresultInvariant, _hposition⟩
        refine ⟨rfl, hvalue.symm, ?_⟩
        rw [ordinaryQueryCache_update_hidden]
        by_cases hcompletable : DeferredCompletable table
            (materializeResolvedPosition context position resolved)
        · exact Or.inl (hinvariant.materialize_resolvedReveal position resolved
            hresultSupport hresultInvariant hcompletable)
        · exact Or.inr ⟨
            hinvariant.2.1.valuesConsistent.materializeResolvedPosition_of table position
              resolved hresultSupport,
            by simpa [materializeResolvedPosition] using
              hinvariant.2.2.1.materialize_position position resolved.output,
            hcompletable⟩
  simpa [materializeResolvedPosition] using hbound

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_revealResolvablePosition_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hresolvable : ResolvableOtsPosition position) :
    RelTriple
      (runResolvedFromTable context fuel table ((revealPosition position).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table position)).run concreteCache)
      (ResolvedStructuralRunRel parameter table) := by
  rw [runResolvedFromTable_revealPosition]
  have hresolve := relTriple_resolveDeferredPosition_chronological parameter table position
    context (ordinaryQueryCache cache) concreteCache hinvariant hresolvable
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolve
      (fun resolved => resolved ∈ support (resolveDeferredPosition table position context))
      (fun resolved hresolved => hresolved)
  have hbound : RelTriple
      (resolveDeferredPosition table position context >>= fun resolved =>
        match resolved with
        | none => pure none
        | some resolved =>
            pure (some ⟨materializeResolvedPosition context position resolved, fuel,
              (truncateHash resolved.output,
                Function.update cache (.hidden (.position position)) (some resolved.output)),
              table⟩))
      (((simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table position)).run concreteCache) >>=
          fun result => pure result)
      (ResolvedStructuralRunRel parameter table) := by
    apply relTriple_bind hsupported
    intro resolved rightResult hrelation
    rcases hrelation with ⟨hresolvedRel, hresultSupport⟩
    cases resolved with
    | none =>
        apply relTriple_pure_pure
        trivial
    | some resolved =>
        apply relTriple_pure_pure
        rcases rightResult with ⟨value, finalCache⟩
        rcases hresolvedRel with ⟨hvalue, hresultInvariant, _hposition⟩
        refine ⟨rfl, hvalue.symm, ?_⟩
        rw [ordinaryQueryCache_update_hidden]
        by_cases hcompletable : DeferredCompletable table
            (materializeResolvedPosition context position resolved)
        · exact Or.inl (hinvariant.materialize_resolvedReveal position resolved
            (by simpa [resolveDeferredReveal, hresolvable] using hresultSupport)
            hresultInvariant hcompletable)
        · have hreveal : some resolved ∈ support
              (resolveDeferredReveal table position context) := by
            simpa [resolveDeferredReveal, hresolvable] using hresultSupport
          exact Or.inr ⟨
            hinvariant.2.1.valuesConsistent.materializeResolvedPosition_of table position
              resolved hreveal,
            by simpa [materializeResolvedPosition] using
              hinvariant.2.2.1.materialize_position position resolved.output,
            hcompletable⟩
  simpa [resolveDeferredReveal, hresolvable, materializeResolvedPosition] using hbound

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_revealResolvablePositionOutput_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (completion : Coordinate → HashOutput) (position : Position) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hcompletion : DeferredCompletion table context completion)
    (hots : IsOtsPosition position)
    (hresolvable : ResolvableOtsPosition position)
    (havailable : TableInputAvailable completion context.state (.position position))
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hinput : input = tableInput parameter completion (.position position)) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((revealCoordinateOutput (.position position)).run cache))
      ((randomOracle input).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  rw [runResolvedFromTable_revealCoordinateOutput]
  have hresolve := relTriple_resolveDeferredPosition_chronological parameter table position
    context (ordinaryQueryCache cache) concreteCache hinvariant hresolvable
  have hrun := resolvedPositionComputation_run_eq_finalQuery_of_available parameter table
    completion context concreteCache position input hcompletion hresolvable havailable hclosed
      hinput
  rw [hrun] at hresolve
  have hsupportedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolve
      (fun resolved => resolved ∈ support (resolveDeferredPosition table position context))
      (fun resolved hresolved => hresolved)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hsupportedLeft
  let recover : Digest × QueryCache HashSpec → HashOutput × QueryCache HashSpec :=
    fun result => ((result.2 input).getD 0, result.2)
  have hcore : RelTriple
      (resolveDeferredPosition table position context >>= fun resolved =>
        match resolved with
        | none => pure none
        | some resolved =>
            pure (some ⟨materializeResolvedPosition context position resolved, fuel,
              (resolved.output,
                Function.update cache (.hidden (.position position)) (some resolved.output)),
              table⟩))
      (((randomOracle input).run concreteCache >>= fun result =>
        pure (truncateHash result.1, result.2)) >>= fun result => pure result)
      (fun left right => ReachableResolvedRunRel parameter table left (recover right)) := by
    apply relTriple_bind hsupported
    intro resolved queryResult hrelation
    rcases hrelation with ⟨⟨hresolvedRel, hresultSupport⟩, hrightSupport⟩
    cases resolved with
    | none =>
        apply relTriple_pure_pure
        trivial
    | some resolved =>
        apply relTriple_pure_pure
        rcases queryResult with ⟨value, finalCache⟩
        rcases hresolvedRel with ⟨_hvalue, hresultInvariant, hposition⟩
        have hpositionSupport : (value, finalCache) ∈ support
            ((simulateQ (randomOracle : QueryImpl HashSpec _)
              (resolvedPositionComputation parameter table position)).run concreteCache) := by
          rw [hrun]
          exact hrightSupport
        have hreplay := replay_of_mem_support
          (resolvedPositionComputation parameter table position) concreteCache value finalCache
            hpositionSupport (fromCache finalCache) (agreesWithFn_fromCache finalCache)
        have hclosedFinal := hclosed.mono hreplay.1
        have hvisible : VisibleResolvedComputationsCached parameter table
            (materializeResolvedPosition context position resolved) finalCache := by
          intro other output hotherResolvable hvisibleValue
          by_cases heq : other = position
          · subst other
            have houtput : output = resolved.output := by
              have houtput' : resolved.output = output := by
                simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize] using
                  hvisibleValue
              exact houtput'.symm
            subst output
            exact ⟨hreplay.2.2, hreplay.2.1.trans _hvalue⟩
          · apply hclosedFinal other output hotherResolvable
            simpa [materializeResolvedPosition, LazyRevealProbe.State.materialize, heq] using
              hvisibleValue
        by_cases hcompletable : DeferredCompletable table
            (materializeResolvedPosition context position resolved)
        · have hcanonical : ∀ otherCompletion,
              DeferredCompletion table resolved.toDeferredContext otherCompletion →
                input = tableInput parameter otherCompletion (.position position) := by
            intro otherCompletion hotherCompletion
            have horiginal := hotherCompletion.of_resolveDeferredPosition
              hinvariant.2.1.valuesConsistent hinvariant.2.2.1 position resolved hresultSupport
            have hotherAvailable := havailable.changeTable horiginal.1
            exact hinput.trans (tableInput_eq_of_available parameter completion otherCompletion
              context.state (.position position) havailable hotherAvailable)
          have hcached : finalCache input = some resolved.output :=
            hresultInvariant.concreteCache_eq_of_positionValue position hots resolved.output
              hposition input hcanonical
          refine Or.inl ⟨rfl, ?_, ?_, hvisible, ?_⟩
          · simp [hcached]
          · rw [ordinaryQueryCache_update_hidden]
            exact hinvariant.materialize_resolvedReveal position resolved
              (by simpa [resolveDeferredReveal, hresolvable] using hresultSupport)
              hresultInvariant hcompletable
          · simpa [materializeResolvedPosition] using
              hpublished.materialize (.position position) resolved.output
        · refine Or.inr ⟨rfl, ?_⟩
          exact ⟨
            hinvariant.2.1.valuesConsistent.materializeResolvedPosition_of table position
              resolved (by simpa [resolveDeferredReveal, hresolvable] using hresultSupport),
            by simpa [materializeResolvedPosition] using
              hinvariant.2.2.1.materialize_position position resolved.output,
            hcompletable⟩
  have hmapped := relTriple_map
    (R := ReachableResolvedRunRel parameter table) (f := id) (g := recover) hcore
  have hrecover : recover <$> (((randomOracle input).run concreteCache >>= fun result =>
        pure (truncateHash result.1, result.2)) >>= fun result => pure result) =
      (randomOracle input).run concreteCache := by
    cases hcache : concreteCache input with
    | none =>
        rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache]
        simp [recover, QueryCache.cacheQuery_self]
    | some output =>
        rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache]
        simp [recover, hcache]
  rw [hrecover] at hmapped
  simpa [resolveDeferredReveal, hresolvable, materializeResolvedPosition] using hmapped

theorem relTriple_runResolvedFromTable_revealChainStart_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((revealChainStart index.lay index.tree index.leafIdx index.chainIdx).run cache))
      (pure (truncateHash (table index), concreteCache) :
        ProbComp (Digest × QueryCache HashSpec))
      (ResolvedStructuralRunRel parameter table) := by
  have hclean := hinvariant.2.2.2.1.not_hitAt_chainStart index
  rw [runResolvedFromTable_revealChainStart_of_agrees context fuel table index cache
    hinvariant.2.2.1 hclean]
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, Or.inl ?_⟩
  rw [ordinaryQueryCache_update_hidden]
  exact hinvariant.materialize_chainStart index

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_maskedChainValue_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedChainValue lay tree leafIdx chainIdx digit).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (chainWalk parameter lay tree leafIdx chainIdx 0 digit.val
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))).run concreteCache)
      (ResolvedStructuralRunRel parameter table) := by
  obtain ⟨reservedContext, hreserve, hreservedInvariant⟩ :=
    (resolvedAdministrative_ensureChainPrefix lay tree leafIdx chainIdx digit).run_preserves_invariant
      context cache fuel concreteCache hinvariant
  unfold maskedChainValue
  rw [StateT.run_bind, runResolvedFromTable_bind, hreserve]
  simp only [pure_bind]
  by_cases hzero : digit.val = 0
  · rw [dif_pos hzero]
    have hstart := relTriple_runResolvedFromTable_revealChainStart_chronological
      parameter table ⟨lay, tree, leafIdx, chainIdx⟩ reservedContext fuel cache concreteCache
        hreservedInvariant
    simpa [hzero, chainWalk] using hstart
  · rw [dif_neg hzero]
    let step : ChainStep := ⟨digit.val - 1, by
      have := digit.isLt
      omega⟩
    have hposition :=
      relTriple_runResolvedFromTable_revealResolvablePosition_chronological parameter table
        (.chain lay tree leafIdx chainIdx step) reservedContext fuel cache concreteCache
          hreservedInvariant (by simp [ResolvableOtsPosition])
    have hpositive : 0 < digit.val := Nat.pos_of_ne_zero hzero
    have hsteps : step.val + 1 = digit.val := by
      simp [step]
      omega
    simpa [resolvedPositionComputation, step, hsteps] using hposition

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_maskedTreeNode_chronological
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight)
    (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedTreeNode lay tree level nodeIdx).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          level nodeIdx)).run concreteCache)
      (ResolvedStructuralRunRel parameter table) := by
  obtain ⟨reservedContext, hreserve, hreservedInvariant⟩ :=
    (resolvedAdministrative_ensureTreeNode lay tree level nodeIdx).run_preserves_invariant
      context cache fuel concreteCache hinvariant
  unfold maskedTreeNode
  rw [StateT.run_bind, runResolvedFromTable_bind, hreserve]
  simp only [pure_bind]
  cases level with
  | zero =>
      have hposition :=
        relTriple_runResolvedFromTable_revealResolvablePosition_chronological parameter table
          (.leaf lay tree (leafOfNat nodeIdx)) reservedContext fuel cache concreteCache
            hreservedInvariant (by simp [ResolvableOtsPosition])
      rw [treeNode_zero_eq]
      simpa [resolvedPositionComputation] using hposition
  | succ current =>
      have hcurrent : current < maxLayerHeight := by omega
      simp only [hcurrent, ↓reduceDIte]
      have hnodeLt : nodeIdx < 2 ^ maxLayerHeight := by
        have hpow : 0 < 2 ^ (current + 1) := pow_pos (by omega) _
        nlinarith
      have hnodeVal : (leafOfNat nodeIdx).val = nodeIdx := by
        simp [leafOfNat, Nat.mod_eq_of_lt hnodeLt]
      have hresolvable : ResolvableOtsPosition
          (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) := by
        simp [ResolvableOtsPosition, hnodeVal]
        exact hspan
      have hposition :=
        relTriple_runResolvedFromTable_revealResolvablePosition_chronological parameter table
          (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) reservedContext fuel cache
            concreteCache hreservedInvariant hresolvable
      simpa [resolvedPositionComputation, hnodeVal] using hposition

theorem relTriple_runResolvedFromTable_splitHashQuery_clean_or_doomed
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((splitHashQuery (.ordinary input)).run cache))
      ((randomOracle input).run concreteCache)
      (ResolvedRunRel parameter table) := by
  apply relTriple_post_mono
    (relTriple_runResolvedFromTable_splitHashQuery_stable parameter table input hstable
      context fuel cache concreteCache hinvariant)
  intro leftResult rightResult hrelation
  exact hrelation.to_resolvedRunRel

theorem relTriple_runResolvedFromTable_maskedChainValue_clean_or_doomed
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedChainValue lay tree leafIdx chainIdx digit).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (chainWalk parameter lay tree leafIdx chainIdx 0 digit.val
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))).run concreteCache)
      (ResolvedRunRel parameter table) := by
  apply relTriple_post_mono
    (relTriple_runResolvedFromTable_maskedChainValue_chronological parameter table lay tree
      leafIdx chainIdx digit context fuel cache concreteCache hinvariant)
  intro leftResult rightResult hrelation
  exact hrelation.to_resolvedRunRel

theorem relTriple_runResolvedFromTable_maskedTreeNode_clean_or_doomed
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight)
    (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((maskedTreeNode lay tree level nodeIdx).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          level nodeIdx)).run concreteCache)
      (ResolvedRunRel parameter table) := by
  apply relTriple_post_mono
    (relTriple_runResolvedFromTable_maskedTreeNode_chronological parameter table lay tree level
      nodeIdx hlevel hspan context fuel cache concreteCache hinvariant)
  intro leftResult rightResult hrelation
  exact hrelation.to_resolvedRunRel

theorem resolvedCouples_splitHashQuery
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ResolvedCouples parameter table (splitHashQuery (.ordinary input))
      (randomOracle input) := by
  intro context fuel cache concreteCache hinvariant
  exact relTriple_runResolvedFromTable_splitHashQuery_clean_or_doomed parameter table input
    hstable context fuel cache concreteCache hinvariant

theorem resolvedCouples_probingHashQuery_of_stable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ResolvedCouples parameter table (probingHashQuery parameter input)
      (randomOracle input) := by
  rw [probingHashQuery_eq_splitHashQuery_of_stable parameter input hstable]
  exact resolvedCouples_splitHashQuery parameter table input hstable

theorem resolvedCouples_verifierHashQuery_of_stable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ResolvedCouples parameter table (verifierHashQuery parameter input)
      (randomOracle input) := by
  rw [verifierHashQuery_eq_splitHashQuery_of_stable parameter input hstable]
  exact resolvedCouples_splitHashQuery parameter table input hstable

theorem runResolvedFromTable_peekCoordinate_of_value
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (coordinate : Coordinate) (output : HashOutput)
    (hvalue : context.state.values coordinate = some output) :
    runResolvedFromTable context fuel table ((peekCoordinate coordinate).run cache) =
      pure (some ⟨context, fuel, (some (truncateHash output), cache), table⟩) := by
  unfold peekCoordinate
  rw [StateT.run_bind, runResolvedFromTable_bind, StateT.run_liftM,
    LazyRevealProbe.peekQuery,
    runResolvedFromTable_peek_query_bind]
  simp [hvalue, runResolvedFromTable]

theorem runResolvedFromTable_peekCoordinate_of_none
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (coordinate : Coordinate)
    (hvalue : context.state.values coordinate = none) :
    runResolvedFromTable context fuel table ((peekCoordinate coordinate).run cache) =
      pure (some ⟨context, fuel, (none, cache), table⟩) := by
  unfold peekCoordinate
  rw [StateT.run_bind, runResolvedFromTable_bind, StateT.run_liftM,
    LazyRevealProbe.peekQuery,
    runResolvedFromTable_peek_query_bind]
  simp [hvalue, runResolvedFromTable]

theorem runResolvedFromTable_peekPositionValues_of_values
    (completion : Coordinate → HashOutput) (context : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ∀ positions : List Position,
      (∀ position, position ∈ positions →
        context.state.values (.position position) = some (completion (.position position))) →
      runResolvedFromTable context fuel table ((peekPositionValues positions).run cache) =
        pure (some ⟨context, fuel,
          (some (positions.map (tableValue completion)), cache), table⟩)
  | [], _ => by simp [peekPositionValues, runResolvedFromTable]
  | position :: remaining, hvalues => by
      rw [peekPositionValues, StateT.run_bind, runResolvedFromTable_bind,
        runResolvedFromTable_peekCoordinate_of_value context fuel table cache
          (.position position) (completion (.position position))
          (hvalues position (by simp))]
      simp only [pure_bind]
      rw [StateT.run_bind, runResolvedFromTable_bind,
        runResolvedFromTable_peekPositionValues_of_values completion context fuel table cache
          remaining (fun other hother => hvalues other (by simp [hother]))]
      simp [runResolvedFromTable, tableValue]

theorem runResolvedFromTable_peekPositionValues_of_prefix_values_of_missing
    (completion : Coordinate → HashOutput) (context : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (prior remaining : List Position) (position : Position)
    (hvalues : ∀ other, other ∈ prior →
      context.state.values (.position other) = some (completion (.position other)))
    (hmissing : context.state.values (.position position) = none) :
    runResolvedFromTable context fuel table
        ((peekPositionValues (prior ++ position :: remaining)).run cache) =
      pure (some ⟨context, fuel, (none, cache), table⟩) := by
  induction prior with
  | nil =>
      rw [List.nil_append, peekPositionValues, StateT.run_bind, runResolvedFromTable_bind,
        runResolvedFromTable_peekCoordinate_of_none context fuel table cache
          (.position position) hmissing]
      simp [runResolvedFromTable]
  | cons head tail ih =>
      rw [List.cons_append, peekPositionValues, StateT.run_bind, runResolvedFromTable_bind,
        runResolvedFromTable_peekCoordinate_of_value context fuel table cache (.position head)
          (completion (.position head)) (hvalues head (by simp))]
      simp only [pure_bind]
      rw [StateT.run_bind, runResolvedFromTable_bind,
        ih (fun other hother => hvalues other (by simp [hother]))]
      simp [runResolvedFromTable]

theorem runResolvedFromTable_peekTableInput_of_available
    (parameter : PublicParameter) (completion : Coordinate → HashOutput)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (coordinate : Coordinate)
    (havailable : TableInputAvailable completion context.state coordinate) :
    runResolvedFromTable context fuel table
        ((peekTableInput parameter coordinate).run cache) =
      pure (some ⟨context, fuel,
        (some (tableInput parameter completion coordinate), cache), table⟩) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [TableInputAvailable] at havailable
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero, StateT.run_bind, runResolvedFromTable_bind,
              runResolvedFromTable_peekCoordinate_of_value context fuel table cache
                (.chainStart lay tree leafIdx chainIdx)
                (completion (.chainStart lay tree leafIdx chainIdx))
                (by simpa [TableInputAvailable, hzero] using havailable)]
            simp [runResolvedFromTable, tableInput, tablePayload, hzero]
          · rw [if_neg hzero, StateT.run_bind, runResolvedFromTable_bind,
              runResolvedFromTable_peekPositionValues_of_values completion context fuel table
                cache _ (by simpa [TableInputAvailable, hzero] using havailable)]
            simp [runResolvedFromTable, tableInput, tablePayload, hzero]
      | leaf lay tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp),
            StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_of_values completion context fuel table cache
              _ havailable]
          simp [runResolvedFromTable, tableInput, tablePayload]
      | node lay tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp),
            StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_of_values completion context fuel table cache
              _ havailable]
          simp [runResolvedFromTable, tableInput, tablePayload]
      | ftsLeaf index tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsLeaf index tree leafIdx) (by simp),
            StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_of_values completion context fuel table cache
              _ havailable]
          simp [runResolvedFromTable, tableInput, tablePayload]
      | ftsNode index tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.ftsNode index tree level nodeIdx) (by simp),
            StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_of_values completion context fuel table cache
              _ havailable]
          simp [runResolvedFromTable, tableInput, tablePayload]
      | ftsRoots index =>
          rw [peekTableInput.eq_3 parameter (.ftsRoots index) (by simp),
            StateT.run_bind, runResolvedFromTable_bind,
            runResolvedFromTable_peekPositionValues_of_values completion context fuel table cache
              _ havailable]
          simp [runResolvedFromTable, tableInput, tablePayload]

theorem runResolvedFromTable_peekTableInput_of_unavailable
    (parameter : PublicParameter) (completion : Coordinate → HashOutput)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (coordinate : Coordinate)
    (hcompletion : DeferredCompletion table context completion)
    (hots : ∀ position, coordinate = .position position → IsOtsPosition position)
    (hunavailable : ¬TableInputAvailable completion context.state coordinate) :
    runResolvedFromTable context fuel table
        ((peekTableInput parameter coordinate).run cache) =
      pure (some ⟨context, fuel, (none, cache), table⟩) := by
  have htable : ∀ coordinate output,
      context.state.values coordinate = some output → output = completion coordinate := by
    intro other output hvalue
    exact (hcompletion.1 other output hvalue).symm
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [peekTableInput, runResolvedFromTable]
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero, StateT.run_bind, runResolvedFromTable_bind]
            have hnone : context.state.values (.chainStart lay tree leafIdx chainIdx) = none := by
              cases hvalue : context.state.values (.chainStart lay tree leafIdx chainIdx) with
              | none => rfl
              | some output =>
                  have hsame := htable (.chainStart lay tree leafIdx chainIdx) output hvalue
                  exfalso
                  apply hunavailable
                  simpa [TableInputAvailable, hzero, hsame] using hvalue
            rw [runResolvedFromTable_peekCoordinate_of_none context fuel table cache _ hnone]
            simp [runResolvedFromTable]
          · rw [if_neg hzero, StateT.run_bind, runResolvedFromTable_bind]
            rcases positionValues_or_first_missing completion context.state
              (Position.chain lay tree leafIdx chainIdx step).children
              (fun other output hvalue =>
                htable (.position other) output hvalue) with havailable |
                ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
            · exact (hunavailable (by simpa [TableInputAvailable, hzero] using havailable)).elim
            · rw [hchildren,
                runResolvedFromTable_peekPositionValues_of_prefix_values_of_missing completion
                  context fuel table cache prior remaining child hvalues hmissing]
              simp [runResolvedFromTable]
      | leaf lay tree leafIdx =>
          rw [peekTableInput.eq_3 parameter (.leaf lay tree leafIdx) (by simp),
            StateT.run_bind, runResolvedFromTable_bind]
          rcases positionValues_or_first_missing completion context.state
            (Position.leaf lay tree leafIdx).children (fun other output hvalue =>
              htable (.position other) output hvalue) with havailable |
              ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
          · exact (hunavailable havailable).elim
          · rw [hchildren,
              runResolvedFromTable_peekPositionValues_of_prefix_values_of_missing completion
                context fuel table cache prior remaining child hvalues hmissing]
            simp [runResolvedFromTable]
      | node lay tree level nodeIdx =>
          rw [peekTableInput.eq_3 parameter (.node lay tree level nodeIdx) (by simp),
            StateT.run_bind, runResolvedFromTable_bind]
          rcases positionValues_or_first_missing completion context.state
            (Position.node lay tree level nodeIdx).children (fun other output hvalue =>
              htable (.position other) output hvalue) with havailable |
              ⟨prior, child, remaining, hchildren, hvalues, hmissing⟩
          · exact (hunavailable havailable).elim
          · rw [hchildren,
              runResolvedFromTable_peekPositionValues_of_prefix_values_of_missing completion
                context fuel table cache prior remaining child hvalues hmissing]
            simp [runResolvedFromTable]
      | ftsLeaf index tree leafIdx => simpa [IsOtsPosition] using hots _ rfl
      | ftsNode index tree level nodeIdx => simpa [IsOtsPosition] using hots _ rfl
      | ftsRoots index => simpa [IsOtsPosition] using hots _ rfl

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_resolveKnownInput_completionCanonical
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (completion : Coordinate → HashOutput) (position : Position) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hcompletion : DeferredCompletion table context completion)
    (hots : IsOtsPosition position)
    (hresolvable : ResolvableOtsPosition position)
    (havailable : TableInputAvailable completion context.state (.position position))
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hinput : input = tableInput parameter completion (.position position)) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((resolveKnownInput parameter (.position position) input).run cache))
      ((randomOracle input).run concreteCache)
      (ResolvedRunRel parameter table) := by
  unfold resolveKnownInput
  rw [StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_peekTableInput_of_available parameter completion context fuel table
      cache (.position position) havailable]
  simp only [pure_bind]
  rw [if_pos hinput.symm]
  change RelTriple
      (runResolvedFromTable context fuel table
        ((revealCoordinateOutput (.position position) >>= fun output =>
          publishOrdinaryInput (.position position) input output).run cache))
      ((randomOracle input).run concreteCache)
      (ResolvedRunRel parameter table)
  rw [StateT.run_bind, runResolvedFromTable_bind]
  have hreveal :=
    relTriple_runResolvedFromTable_revealResolvablePositionOutput_chronological parameter table
      completion position input context fuel cache concreteCache hinvariant hcompletion hots
        hresolvable havailable hclosed hpublished hinput
  have hsupportedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hreveal
      (fun result => result ∈ support
        (runResolvedFromTable context fuel table
          ((revealCoordinateOutput (.position position)).run cache)))
      (fun result hresult => hresult)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hsupportedLeft
  rw [show (randomOracle input).run concreteCache =
      ((randomOracle input).run concreteCache >>= fun result => pure result) by simp]
  apply relTriple_bind hsupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | none =>
      apply relTriple_pure_pure
      trivial
  | some result =>
      rcases hrelation with hclean | hdoomed
      · have hcached : rightResult.2 input = some rightResult.1 :=
          randomOracle_run_output_cached input concreteCache rightResult.2 rightResult.1
            hrightSupport
        simpa [hclean.1, hclean.2.1] using
          (relTriple_runResolvedFromTable_publishOrdinaryInput parameter table
            (.position position) input rightResult.1 result.context result.remaining
              result.value.2 rightResult.2 hclean.2.2.1 hcached)
      · simpa [hdoomed.1] using
          (relTriple_runResolvedFromTable_of_doomed parameter table
            (publishOrdinaryInput (.position position) input result.value.1)
            (pure rightResult) result.context result.remaining result.value.2 hdoomed.2)

theorem relTriple_runResolvedFromTable_resolveKnownInput_completionOrdinary
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hots : ∀ position, coordinate = .position position → IsOtsPosition position)
    (hordinary : CompletionOrdinaryInput parameter table context input) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((resolveKnownInput parameter coordinate input).run cache))
      ((randomOracle input).run concreteCache)
      (ResolvedOrdinaryRunRel parameter table) := by
  obtain ⟨completion, hcompletion⟩ := hinvariant.2.2.2.1
  unfold resolveKnownInput
  rw [StateT.run_bind, runResolvedFromTable_bind]
  by_cases havailable : TableInputAvailable completion context.state coordinate
  · rw [runResolvedFromTable_peekTableInput_of_available parameter completion context fuel table
      cache coordinate havailable]
    simp only [pure_bind]
    have hne : tableInput parameter completion coordinate ≠ input := by
      intro heq
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp [TableInputAvailable] at havailable
      | position position =>
          exact hordinary completion hcompletion position (hots position rfl) heq.symm
    rw [if_neg hne]
    exact relTriple_runResolvedFromTable_splitHashQuery_completionOrdinary parameter table input
      context hordinary fuel cache concreteCache hinvariant
  · rw [runResolvedFromTable_peekTableInput_of_unavailable parameter completion context fuel table
      cache coordinate hcompletion hots havailable]
    simp only [pure_bind]
    exact relTriple_runResolvedFromTable_splitHashQuery_completionOrdinary parameter table input
      context hordinary fuel cache concreteCache hinvariant

theorem relTriple_runResolvedFromTable_publishOrdinaryInput_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (input : HashInput) (output : HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hvalue : context.state.values coordinate ≠ none)
    (hconcrete : concreteCache input = some output) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((publishOrdinaryInput coordinate input output).run cache))
      (pure (output, concreteCache) : ProbComp (HashOutput × QueryCache HashSpec))
      (ReachableResolvedRunRel parameter table) := by
  unfold publishOrdinaryInput publishCoordinate
  rw [StateT.run_bind, runResolvedFromTable_bind, StateT.run_liftM,
    LazyRevealProbe.publishQuery, runResolvedFromTable_publish_query_bind]
  simp only [runResolvedFromTable, pure_bind]
  apply relTriple_pure_pure
  refine Or.inl ⟨rfl, rfl, ?_, hclosed.of_state_values_eq rfl, ?_⟩
  · rw [ordinaryQueryCache_update]
    exact hinvariant.cacheLeft_of_concrete input output hconcrete
  · intro other hrevealed
    simp only [LazyRevealProbe.State.publish, Finset.mem_insert] at hrevealed
    rcases hrevealed with heq | hrevealed
    · subst other
      exact hvalue
    · exact hpublished other hrevealed

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_resolveKnownInput_completionCanonical_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (completion : Coordinate → HashOutput) (position : Position) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hcompletion : DeferredCompletion table context completion)
    (hots : IsOtsPosition position)
    (hresolvable : ResolvableOtsPosition position)
    (havailable : TableInputAvailable completion context.state (.position position))
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hinput : input = tableInput parameter completion (.position position)) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((resolveKnownInput parameter (.position position) input).run cache))
      ((randomOracle input).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  unfold resolveKnownInput
  rw [StateT.run_bind, runResolvedFromTable_bind,
    runResolvedFromTable_peekTableInput_of_available parameter completion context fuel table
      cache (.position position) havailable]
  simp only [pure_bind]
  rw [if_pos hinput.symm]
  change RelTriple
      (runResolvedFromTable context fuel table
        ((revealCoordinateOutput (.position position) >>= fun output =>
          publishOrdinaryInput (.position position) input output).run cache))
      ((randomOracle input).run concreteCache)
      (ReachableResolvedRunRel parameter table)
  rw [StateT.run_bind, runResolvedFromTable_bind]
  have hreveal :=
    relTriple_runResolvedFromTable_revealResolvablePositionOutput_chronological parameter table
      completion position input context fuel cache concreteCache hinvariant hcompletion hots
        hresolvable havailable hclosed hpublished hinput
  have hsupportedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hreveal
      (fun result => result ∈ support
        (runResolvedFromTable context fuel table
          ((revealCoordinateOutput (.position position)).run cache)))
      (fun result hresult => hresult)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hsupportedLeft
  rw [show (randomOracle input).run concreteCache =
      ((randomOracle input).run concreteCache >>= fun result => pure result) by simp]
  apply relTriple_bind hsupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | none =>
      apply relTriple_pure_pure
      trivial
  | some result =>
      rcases hrelation with hclean | hdoomed
      · have hcached : rightResult.2 input = some rightResult.1 :=
          randomOracle_run_output_cached input concreteCache rightResult.2 rightResult.1
            hrightSupport
        simpa [hclean.1, hclean.2.1] using
          (relTriple_runResolvedFromTable_publishOrdinaryInput_reachable parameter table
            (.position position) input rightResult.1 result.context result.remaining
              result.value.2 rightResult.2 hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
                (by
                  rw [value_of_mem_runResolvedFromTable_revealCoordinateOutput context fuel table
                    (.position position) cache result hleftSupport]
                  simp)
                hcached)
      · simpa [hdoomed.1] using
          (relTriple_runResolvedFromTable_of_doomed_reachable parameter table
            (publishOrdinaryInput (.position position) input result.value.1)
            (pure rightResult) result.context result.remaining result.value.2 hdoomed.2)

theorem relTriple_runResolvedFromTable_resolveKnownInput_completionOrdinary_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (coordinate : Coordinate) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hots : ∀ position, coordinate = .position position → IsOtsPosition position)
    (hordinary : CompletionOrdinaryInput parameter table context input) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((resolveKnownInput parameter coordinate input).run cache))
      ((randomOracle input).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  obtain ⟨completion, hcompletion⟩ := hinvariant.2.2.2.1
  unfold resolveKnownInput
  rw [StateT.run_bind, runResolvedFromTable_bind]
  by_cases havailable : TableInputAvailable completion context.state coordinate
  · rw [runResolvedFromTable_peekTableInput_of_available parameter completion context fuel table
      cache coordinate havailable]
    simp only [pure_bind]
    have hne : tableInput parameter completion coordinate ≠ input := by
      intro heq
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp [TableInputAvailable] at havailable
      | position position =>
          exact hordinary completion hcompletion position (hots position rfl) heq.symm
    rw [if_neg hne]
    exact relTriple_runResolvedFromTable_splitHashQuery_completionOrdinary_reachable parameter
      table input context hordinary fuel cache concreteCache hinvariant hclosed hpublished
  · rw [runResolvedFromTable_peekTableInput_of_unavailable parameter completion context fuel table
      cache coordinate hcompletion hots havailable]
    simp only [pure_bind]
    exact relTriple_runResolvedFromTable_splitHashQuery_completionOrdinary_reachable parameter
      table input context hordinary fuel cache concreteCache hinvariant hclosed hpublished

theorem completionOrdinaryInput_of_available_decoded_ne
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {completion : Coordinate → HashOutput}
    {position : Position} {input : HashInput}
    (hdecode : decodePosition? parameter input = some position)
    (havailable : TableInputAvailable completion context.state (.position position))
    (hne : tableInput parameter completion (.position position) ≠ input) :
    CompletionOrdinaryInput parameter table context input := by
  intro otherCompletion hotherCompletion otherPosition _hots heq
  have hdecodeOther : decodePosition? parameter input = some otherPosition := by
    rw [heq]
    exact (decodePosition?_eq_some_iff parameter _ otherPosition).2
      ⟨tablePayload otherCompletion otherPosition, rfl⟩
  have hposition : otherPosition = position := by
    rw [hdecode] at hdecodeOther
    exact Option.some.inj hdecodeOther.symm
  subst otherPosition
  have hotherAvailable := havailable.changeTable hotherCompletion.1
  have htable := tableInput_eq_of_available parameter completion otherCompletion context.state
    (.position position) havailable hotherAvailable
  exact hne (htable.trans heq.symm)

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_resolveKnownInput_availableDecoded_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state)
    (hots : IsOtsPosition position)
    (hresolvable : ResolvableOtsPosition position)
    (hdecode : decodePosition? parameter input = some position)
    (completion : Coordinate → HashOutput)
    (hcompletion : DeferredCompletion table context completion)
    (havailable : TableInputAvailable completion context.state (.position position)) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((resolveKnownInput parameter (.position position) input).run cache))
      ((randomOracle input).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  by_cases hinput : tableInput parameter completion (.position position) = input
  · exact relTriple_runResolvedFromTable_resolveKnownInput_completionCanonical_reachable
      parameter table completion position input context fuel cache concreteCache hinvariant
        hcompletion hots hresolvable havailable hclosed hpublished hinput.symm
  · exact relTriple_runResolvedFromTable_resolveKnownInput_completionOrdinary_reachable
      parameter table (.position position) input context fuel cache concreteCache hinvariant hclosed
        hpublished (fun other heq => by cases heq; exact hots)
        (completionOrdinaryInput_of_available_decoded_ne hdecode havailable hinput)

theorem tableInputAvailable_chain_of_probe_revealed
    {parameter : PublicParameter} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {completion : Coordinate → HashOutput}
    {input : HashInput} {candidate : Probe}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    {chainIdx : ChainIndex} {step : ChainStep}
    (hcompletion : DeferredCompletion table context completion)
    (hpublished : PublishedValues context.state)
    (hmatches : candidate.MatchesInput parameter input)
    (houtput : candidate.outputCoordinate =
      .position (.chain lay tree leafIdx chainIdx step))
    (hrevealed : candidate.coordinate ∈ context.state.revealed) :
    TableInputAvailable completion context.state
      (.position (.chain lay tree leafIdx chainIdx step)) := by
  obtain ⟨sourceOutput, hsourceValue⟩ :=
    Option.ne_none_iff_exists'.mp (hpublished candidate.coordinate hrevealed)
  have hsourceTable := hcompletion.1 candidate.coordinate sourceOutput hsourceValue
  rw [← houtput]
  rcases candidate with ⟨coordinate, candidateDigest⟩
  cases coordinate with
  | chainStart sourceLay sourceTree sourceLeaf sourceChain =>
      rcases hmatches with ⟨_sourceStep, _hzero, _hinput⟩
      simp [Probe.outputCoordinate, TableInputAvailable, hsourceTable, hsourceValue]
  | position source =>
      cases source with
      | chain sourceLay sourceTree sourceLeaf sourceChain sourceStep =>
          simp only [Probe.MatchesInput] at hmatches
          by_cases hnext : sourceStep.val + 1 < chainLength - 1
          · rw [dif_pos hnext] at hmatches
            rcases hmatches with ⟨_nextStep, _hnextValue, _hinput⟩
            simp [Probe.outputCoordinate, hnext, TableInputAvailable, Position.children,
              hsourceTable, hsourceValue]
          · simp [Probe.outputCoordinate, hnext] at houtput
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp [Probe.MatchesInput] at hmatches

set_option maxRecDepth 100000 in
theorem relTriple_runResolvedFromTable_probingHashQuery_chain_reachable
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep)
    (hprobe : decodeProbe? parameter input = some candidate)
    (hposition : decodePosition? parameter input =
      some (.chain lay tree leafIdx chainIdx step))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (concreteCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context
      (ordinaryQueryCache cache) concreteCache)
    (hclosed : VisibleResolvedComputationsCached parameter table context concreteCache)
    (hpublished : PublishedValues context.state) :
    RelTriple
      (runResolvedFromTable context fuel table
        ((probingHashQuery parameter input).run cache))
      ((randomOracle input).run concreteCache)
      (ReachableResolvedRunRel parameter table) := by
  have hmatches := (decodeProbe?_eq_some_iff parameter input candidate).1 hprobe
  have houtput := decodeProbe?_outputCoordinate_eq_position parameter input candidate
    (.chain lay tree leafIdx chainIdx step) hprobe hposition
  unfold probingHashQuery
  rw [hprobe, hposition]
  simp only
  rw [houtput, StateT.run_bind, runResolvedFromTable_bind]
  unfold probe
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedFromTable_probe_query_bind]
  cases fuel with
  | zero =>
      have hbase := relTriple_true
        (pure (none : Option (ResolvedRunResult (HashOutput × SplitHashCache))) :
          ProbComp (Option (ResolvedRunResult (HashOutput × SplitHashCache))))
        ((randomOracle input).run concreteCache)
      have hsupported :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun result => result = none) (by
            intro result hresult
            simpa using hresult)
      apply relTriple_post_mono hsupported
      intro leftResult _ hrelation
      rw [hrelation.2]
      trivial
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simp only [hrevealed, ↓reduceIte]
        obtain ⟨completion, hcompletion⟩ := hinvariant.2.2.2.1
        have havailable := tableInputAvailable_chain_of_probe_revealed hcompletion hpublished
          hmatches houtput hrevealed
        exact relTriple_runResolvedFromTable_resolveKnownInput_availableDecoded_reachable
          parameter table (.chain lay tree leafIdx chainIdx step) input context remaining cache
            concreteCache hinvariant hclosed hpublished (by simp [IsOtsPosition])
              (by simp [ResolvableOtsPosition]) hposition completion hcompletion havailable
      · simp only [hrevealed, ↓reduceIte]
        let probeContext : DeferredContext :=
          { context with state :=
              context.state.addPending candidate.coordinate candidate.candidate }
        by_cases hcompletable : DeferredCompletable table probeContext
        · have hprobeInvariant := hinvariant.addPending_of_completable
            candidate.coordinate candidate.candidate hcompletable
          have hprobeClosed : VisibleResolvedComputationsCached parameter table probeContext
              concreteCache := hclosed.of_state_values_eq rfl
          have hprobePublished : PublishedValues probeContext.state := by
            simpa [probeContext, PublishedValues, LazyRevealProbe.State.addPending] using hpublished
          have hpending : (candidate.coordinate, candidate.candidate) ∈
              probeContext.state.pending := by
            simp [probeContext, LazyRevealProbe.State.addPending]
          have hordinary := completionOrdinaryInput_of_pending_decodedProbe (table := table)
            hprobe hpending
          exact relTriple_runResolvedFromTable_resolveKnownInput_completionOrdinary_reachable
            parameter table (.position (.chain lay tree leafIdx chainIdx step)) input
              probeContext remaining cache concreteCache hprobeInvariant hprobeClosed hprobePublished
                (fun position heq => by cases heq; simp [IsOtsPosition]) hordinary
        · have hdoomed : DoomedResolvedContext table probeContext := ⟨
            hinvariant.2.1.valuesConsistent.addPending candidate.coordinate candidate.candidate,
            hinvariant.2.2.1.addPending candidate.coordinate candidate.candidate,
            hcompletable⟩
          exact relTriple_runResolvedFromTable_of_doomed_reachable parameter table
            (resolveKnownInput parameter (.position (.chain lay tree leafIdx chainIdx step)) input)
              ((randomOracle input).run concreteCache) probeContext remaining cache hdoomed

theorem resolvedCouples_revealChainStart
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : OtsSecretIndex) :
    ResolvedCouples parameter table
      (revealChainStart index.lay index.tree index.leafIdx index.chainIdx)
      (pure (truncateHash (table index)) : StateT (QueryCache HashSpec) ProbComp Digest) := by
  intro context fuel cache concreteCache hinvariant
  apply relTriple_post_mono
    (relTriple_runResolvedFromTable_revealChainStart_chronological parameter table index context
      fuel cache concreteCache hinvariant)
  intro leftResult rightResult hrelation
  exact hrelation.to_resolvedRunRel

theorem resolvedCouples_revealResolvablePosition
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (position : Position) (hresolvable : ResolvableOtsPosition position) :
    ResolvedCouples parameter table (revealPosition position)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (resolvedPositionComputation parameter table position)) := by
  intro context fuel cache concreteCache hinvariant
  apply relTriple_post_mono
    (relTriple_runResolvedFromTable_revealResolvablePosition_chronological parameter table
      position context fuel cache concreteCache hinvariant hresolvable)
  intro leftResult rightResult hrelation
  exact hrelation.to_resolvedRunRel

theorem resolvedCouples_revealPublishedChainValue
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    ResolvedCouples parameter table
      (revealPublishedCoordinate
        (chainValueCoordinate lay tree leafIdx chainIdx digit))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (chainWalk parameter lay tree leafIdx chainIdx 0 digit.val
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))) := by
  unfold revealPublishedCoordinate chainValueCoordinate
  split
  · have hbase := (resolvedCouples_revealChainStart parameter table
      ⟨lay, tree, leafIdx, chainIdx⟩).bind fun value =>
        (resolvedCouples_of_administrative
          (resolvedAdministrative_publishCoordinate
            (.chainStart lay tree leafIdx chainIdx))).bind fun _ =>
            resolvedCouples_pure parameter table value
    simpa [revealChainStart, chainWalk, ‹digit.val = 0›] using hbase
  · let step : ChainStep := ⟨digit.val - 1, by
      have := digit.isLt
      omega⟩
    have hwalk : resolvedPositionComputation parameter table
        (.chain lay tree leafIdx chainIdx step) =
        chainWalk parameter lay tree leafIdx chainIdx 0 digit.val
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) := by
      simp [resolvedPositionComputation, step]
      have hpos : 0 < digit.val := Nat.pos_of_ne_zero ‹digit.val ≠ 0›
      congr 1
      omega
    rw [← hwalk]
    have hbase := (resolvedCouples_revealResolvablePosition parameter table
      (.chain lay tree leafIdx chainIdx step) (by simp [ResolvableOtsPosition])).bind fun value =>
        (resolvedCouples_of_administrative
          (resolvedAdministrative_publishCoordinate
            (.position (.chain lay tree leafIdx chainIdx step)))).bind fun _ =>
            resolvedCouples_pure parameter table value
    simpa [revealPosition, step] using hbase

theorem resolvedCouples_revealPublishedTreeNode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight)
    (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    ResolvedCouples parameter table
      (match level with
        | 0 => revealPublishedCoordinate (.position (.leaf lay tree (leafOfNat nodeIdx)))
        | current + 1 =>
            if hcurrent : current < maxLayerHeight then
              revealPublishedCoordinate (.position
                (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)))
            else pure 0)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          level nodeIdx)) := by
  cases level with
  | zero =>
      have hbase := (resolvedCouples_revealResolvablePosition parameter table
        (.leaf lay tree (leafOfNat nodeIdx)) (by simp [ResolvableOtsPosition])).bind fun value =>
          (resolvedCouples_of_administrative
            (resolvedAdministrative_publishCoordinate
              (.position (.leaf lay tree (leafOfNat nodeIdx))))).bind fun _ =>
                resolvedCouples_pure parameter table value
      simpa [revealPublishedCoordinate, revealPosition, resolvedPositionComputation,
        treeNode_zero_eq] using hbase
  | succ current =>
      have hcurrent : current < maxLayerHeight := by omega
      simp only [hcurrent, ↓reduceDIte]
      have hnodeLt : nodeIdx < 2 ^ maxLayerHeight := by
        have hpow : 0 < 2 ^ (current + 1) := pow_pos (by omega) _
        nlinarith
      have hnodeVal : (leafOfNat nodeIdx).val = nodeIdx := by
        simp [leafOfNat, Nat.mod_eq_of_lt hnodeLt]
      have hresolvable : ResolvableOtsPosition
          (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) := by
        simp [ResolvableOtsPosition, hnodeVal]
        exact hspan
      have hbase := (resolvedCouples_revealResolvablePosition parameter table
        (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) hresolvable).bind fun value =>
          (resolvedCouples_of_administrative
            (resolvedAdministrative_publishCoordinate
              (.position (.node lay tree ⟨current, hcurrent⟩
                (leafOfNat nodeIdx))))).bind fun _ =>
                  resolvedCouples_pure parameter table value
      simpa [revealPublishedCoordinate, revealPosition, resolvedPositionComputation,
        hnodeVal] using hbase

theorem resolvedCouples_revealLayerPathNode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (lay : Layer) (level : Fin maxLayerHeight) :
    ResolvedCouples parameter table
      (if level.val < layerHeight lay then
        match level.val with
        | 0 => revealPublishedCoordinate (.position (.leaf lay (treeIndexAt index lay)
            (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | current + 1 =>
            if hcurrent : current < maxLayerHeight then
              revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                ⟨current, hcurrent⟩ (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            else pure 0
      else pure 0)
      (if level.val < layerHeight lay then
        simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeNode parameter lay (treeIndexAt index lay)
            (fun sibling chainIdx =>
              truncateHash (table ⟨lay, treeIndexAt index lay, sibling, chainIdx⟩))
            level.val
            (Nat.xor ((leafIndexAt index lay).val / 2 ^ level.val) 1))
      else pure 0) := by
  by_cases hinLayer : level.val < layerHeight lay
  · rw [if_pos hinLayer, if_pos hinLayer]
    cases hvalue : level.val with
    | zero =>
        simpa [hvalue] using
          resolvedCouples_revealPublishedTreeNode parameter table lay
            (treeIndexAt index lay) 0
            (Nat.xor (leafIndexAt index lay).val 1) (by omega)
            (by
              simpa using (FtsProbeSimulation.sibling_node_bound maxLayerHeight
                (leafIndexAt index lay).val 0 (by omega) (leafIndexAt index lay).isLt))
    | succ current =>
        have hcurrent : current < maxLayerHeight := by
          have := level.isLt
          omega
        simpa [hvalue, hcurrent] using
          resolvedCouples_revealPublishedTreeNode parameter table lay
            (treeIndexAt index lay) (current + 1)
            (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1)
            (by omega)
            (FtsProbeSimulation.sibling_node_bound maxLayerHeight
              (leafIndexAt index lay).val (current + 1) (by omega)
              (leafIndexAt index lay).isLt)
  · rw [if_neg hinLayer, if_neg hinLayer]
    exact resolvedCouples_pure parameter table 0

set_option maxHeartbeats 400000 in
theorem resolvedCouples_revealLayerValues
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    ResolvedCouples parameter table (revealLayerValues index lay encoding)
      (do
        let tree := treeIndexAt index lay
        let leafIdx := leafIndexAt index lay
        let values ← sequenceFin fun chainIdx =>
          simulateQ (randomOracle : QueryImpl HashSpec _)
            (chainWalk parameter lay tree leafIdx chainIdx 0 (encoding chainIdx).val
              (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))
        let path ← sequenceFin fun level : Fin maxLayerHeight =>
          if level.val < layerHeight lay then
            simulateQ (randomOracle : QueryImpl HashSpec _)
              (treeNode parameter lay tree
                (fun sibling chainIdx =>
                  truncateHash (table ⟨lay, tree, sibling, chainIdx⟩))
                level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1))
          else
            pure 0
        pure (values, path)) := by
  unfold revealLayerValues
  apply (resolvedCouples_sequenceFin _ _ fun chainIdx =>
    resolvedCouples_revealPublishedChainValue parameter table lay (treeIndexAt index lay)
      (leafIndexAt index lay) chainIdx (encoding chainIdx)).bind
  intro values
  apply (resolvedCouples_sequenceFin _ _ fun level =>
    resolvedCouples_revealLayerPathNode parameter table index lay level).bind
  intro path
  exact resolvedCouples_pure parameter table (values, path)

noncomputable def resolvedRevealLayerValues
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    StateT (QueryCache HashSpec) ProbComp
      ((ChainIndex → Digest) × (Fin maxLayerHeight → Digest)) := do
  let tree := treeIndexAt index lay
  let leafIdx := leafIndexAt index lay
  let values ← sequenceFin fun chainIdx =>
    simulateQ (randomOracle : QueryImpl HashSpec _)
      (chainWalk parameter lay tree leafIdx chainIdx 0 (encoding chainIdx).val
        (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))
  let path ← sequenceFin fun level : Fin maxLayerHeight =>
    if level.val < layerHeight lay then
      simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun sibling chainIdx =>
            truncateHash (table ⟨lay, tree, sibling, chainIdx⟩))
          level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1))
    else
      pure 0
  pure (values, path)

theorem resolvedCouples_resolvedRevealLayerValues
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    ResolvedCouples parameter table (revealLayerValues index lay encoding)
      (resolvedRevealLayerValues parameter table index lay encoding) := by
  unfold resolvedRevealLayerValues
  exact resolvedCouples_revealLayerValues parameter table index lay encoding

theorem resolvedCouples_oracleHash
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (oracleHash input))
      (simulateQ (randomOracle : QueryImpl HashSpec _) (oracleHash input)) := by
  simpa only [oracleHash, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    ordinaryHashImpl] using
    resolvedCouples_splitHashQuery parameter table input hstable

theorem resolvedCouples_tweakableHash
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (domain : HashDomain) (payload : HashInput)
    (hstable : StableOrdinaryInput parameter
      (tweakableHashInput parameter domain payload)) :
    ResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (tweakableHash parameter domain payload))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (tweakableHash parameter domain payload)) := by
  unfold tweakableHash
  rw [simulateQ_bind, simulateQ_bind]
  exact (resolvedCouples_oracleHash parameter table
    (tweakableHashInput parameter domain payload) hstable).bind fun output =>
      resolvedCouples_pure parameter table (truncateHash output)

theorem resolvedCouples_ftsLeafHash
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) (secret : Digest) :
    ResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (ftsLeafHash parameter index tree leafIdx secret))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsLeafHash parameter index tree leafIdx secret)) := by
  unfold ftsLeafHash
  exact resolvedCouples_tweakableHash parameter table (.ftsLeaf index tree leafIdx) _
    (stableOrdinaryInput_tweakableHashInput parameter (.ftsLeaf index tree leafIdx) _
      (by trivial) (by simp) (by simp) (by simp))

theorem simulateQ_ordinaryHashImpl_sequenceFin {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha) :
    simulateQ ordinaryHashImpl (sequenceFin computation) =
      sequenceFin fun position => simulateQ ordinaryHashImpl (computation position) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      simp only [sequenceFin, simulateQ_bind, simulateQ_pure, ih]

theorem resolvedCouples_ftsNode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) :
    ∀ level nodeIdx, level ≤ ftsTreeHeight →
      2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight →
      ResolvedCouples parameter table
        (simulateQ ordinaryHashImpl
          (ftsNode parameter index tree secret level nodeIdx))
        (simulateQ (randomOracle : QueryImpl HashSpec _)
          (ftsNode parameter index tree secret level nodeIdx))
  | 0, nodeIdx, hlevel, hspan => by
      rw [ftsNode_zero_eq]
      exact resolvedCouples_ftsLeafHash parameter table index tree _ _
  | level + 1, nodeIdx, hlevel, hspan => by
      rw [ftsNode_succ_eq]
      simp only [simulateQ_bind]
      have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ level * (2 * (nodeIdx + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ level * 2 * (nodeIdx + 1) := by ring
          _ ≤ 2 ^ ftsTreeHeight := hspan
      have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1 + 1) = 2 ^ level * 2 * (nodeIdx + 1) := by
            ring
          _ ≤ 2 ^ ftsTreeHeight := hspan
      have hinRange : (HashDomain.ftsNode index tree (level + 1) nodeIdx).InRange := by
        show level + 1 < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
        constructor
        · have : ftsTreeHeight < 2 ^ 32 := by norm_num [ftsTreeHeight]
          omega
        · have hnode : nodeIdx < 2 ^ ftsTreeHeight := by
            have hpow : 0 < 2 ^ (level + 1) := Nat.two_pow_pos _
            nlinarith
          have : 2 ^ ftsTreeHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by
            norm_num [ftsTreeHeight])
          omega
      exact (resolvedCouples_ftsNode parameter table index tree secret level (2 * nodeIdx)
        (by omega) hleftSpan).bind fun left =>
          (resolvedCouples_ftsNode parameter table index tree secret level (2 * nodeIdx + 1)
            (by omega) hrightSpan).bind fun right =>
              resolvedCouples_tweakableHash parameter table
                (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)
                (stableOrdinaryInput_tweakableHashInput parameter
                  (.ftsNode index tree (level + 1) nodeIdx) _ hinRange
                  (by simp) (by simp) (by simp))

theorem resolvedCouples_ftsKey
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    ResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (ftsKey parameter index secret))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsKey parameter index secret)) := by
  unfold ftsKey
  rw [simulateQ_bind, simulateQ_bind, simulateQ_ordinaryHashImpl_sequenceFin,
    FtsProbeSimulation.simulateQ_randomOracle_sequenceFin]
  exact (resolvedCouples_sequenceFin
    (fun tree => simulateQ ordinaryHashImpl
      (ftsNode parameter index tree (secret tree) ftsTreeHeight 0))
    (fun tree => simulateQ (randomOracle : QueryImpl HashSpec _)
      (ftsNode parameter index tree (secret tree) ftsTreeHeight 0))
    (fun tree => resolvedCouples_ftsNode parameter table index tree (secret tree)
      ftsTreeHeight 0 le_rfl (by simp))).bind fun roots =>
        resolvedCouples_tweakableHash parameter table (.ftsRoots index)
          (ftsRootsPayload roots)
          (stableOrdinaryInput_tweakableHashInput parameter (.ftsRoots index) _
            (by trivial) (by simp) (by simp) (by simp))

theorem resolvedCouples_ftsOpen
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (leaves : DigestTree → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    ResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (ftsOpen parameter index leaves secret))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsOpen parameter index leaves secret)) := by
  unfold ftsOpen
  rw [simulateQ_ordinaryHashImpl_sequenceFin,
    FtsProbeSimulation.simulateQ_randomOracle_sequenceFin]
  exact resolvedCouples_sequenceFin _ _ fun tree => by
    rw [simulateQ_ordinaryHashImpl_sequenceFin,
      FtsProbeSimulation.simulateQ_randomOracle_sequenceFin]
    exact resolvedCouples_sequenceFin _ _ fun level =>
      resolvedCouples_ftsNode parameter table index tree (secret tree) level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)
        (Nat.le_of_lt level.isLt)
        (FtsProbeSimulation.ftsOpen_node_bound (leaves (ftsIndexOf tree)) level)

theorem resolvedCouples_encode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    ResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (encode parameter lay tree leafIdx message counter))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (encode parameter lay tree leafIdx message counter)) := by
  unfold encode
  rw [simulateQ_bind, simulateQ_bind]
  exact (resolvedCouples_tweakableHash parameter table (.encoding lay tree leafIdx) _
    (stableOrdinaryInput_tweakableHashInput parameter (.encoding lay tree leafIdx) _
      (by trivial) (by simp) (by simp) (by simp))).bind fun digest =>
        resolvedCouples_pure parameter table (TargetSum.decodeDigest digest)

theorem resolvedCouples_messageDigest
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (root : Digest) (message : Message) (randomness : Randomness) :
    ResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (messageDigest parameter root message randomness))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (messageDigest parameter root message randomness)) := by
  unfold messageDigest
  rw [simulateQ_bind, simulateQ_bind]
  exact (resolvedCouples_oracleHash parameter table
    (tweakableHashInput parameter .message
      (messageDigestPayload root message randomness))
    (stableOrdinaryInput_tweakableHashInput parameter .message _
      (by trivial) (by simp) (by simp) (by simp))).bind fun output =>
        resolvedCouples_pure parameter table (truncateMessageDigest output)

theorem resolvedCouples_signAttempt
    (table : OtsSecretIndex → HashOutput) (secretKey : SecretKey)
    (message : Message) (randomness : Randomness) :
    ResolvedCouples secretKey.parameter table
      (simulateQ ordinaryHashImpl (signAttempt secretKey message randomness))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)) := by
  unfold signAttempt
  simp only [simulateQ_bind]
  exact (resolvedCouples_messageDigest secretKey.parameter table secretKey.root message
    randomness).bind fun digest => by
      split <;> exact resolvedCouples_pure secretKey.parameter table _

theorem resolvedCouples_signDigestLoop
    (table : OtsSecretIndex → HashOutput) (secretKey : SecretKey)
    (message : Message) : ∀ attempts,
    ResolvedCouples secretKey.parameter table
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message))
      (simulateQ romImpl (signDigestLoop attempts secretKey message))
  | 0 => by
      rw [signDigestLoop, simulateQ_pure, simulateQ_pure]
      exact resolvedCouples_pure secretKey.parameter table none
  | attempts + 1 => by
      rw [signDigestLoop, simulateQ_bind, simulateQ_bind]
      have hrandomness : ResolvedCouples secretKey.parameter table
          (simulateQ ordinaryRomImpl (liftM sampleRandomness))
          (simulateQ romImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, romImpl, QueryImpl.simulateQ_add_liftM_left,
          QueryImpl.simulateQ_add_liftM_left]
        exact resolvedCouples_simulateQ splitUniformImpl (unifFwdImpl HashSpec)
          (resolvedCouples_splitUniform secretKey.parameter table) sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind, simulateQ_bind]
        have hattempt : ResolvedCouples secretKey.parameter table
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))))
            (simulateQ romImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, romImpl, QueryImpl.simulateQ_add_liftM_right,
            QueryImpl.simulateQ_add_liftM_right]
          exact resolvedCouples_signAttempt table secretKey message randomness
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none => exact resolvedCouples_signDigestLoop table secretKey message attempts
          | some selected => exact resolvedCouples_pure secretKey.parameter table _

noncomputable def resolvedOtsSelectFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : Nat → Nat →
    StateT (QueryCache HashSpec) ProbComp
      (Option (Counter × (ChainIndex → Digit)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      let encoded ← simulateQ (randomOracle : QueryImpl HashSpec _)
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))
      match encoded with
      | some encoding => pure (some (BitVec.ofNat counterBits counter, encoding))
      | none =>
          resolvedOtsSelectFrom parameter lay tree leafIdx message attempts (counter + 1)

noncomputable def resolvedOtsSelect
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    StateT (QueryCache HashSpec) ProbComp
      (Option (Counter × (ChainIndex → Digit))) :=
  resolvedOtsSelectFrom parameter lay tree leafIdx message encodingAttemptLimit 0

theorem resolvedCouples_maskedOtsSignFrom
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      ResolvedCouples parameter table
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
        (resolvedOtsSelectFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom, resolvedOtsSelectFrom]
      exact resolvedCouples_pure parameter table none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom, resolvedOtsSelectFrom]
      exact (resolvedCouples_encode parameter table lay tree leafIdx message
        (BitVec.ofNat counterBits counter)).bind fun encoded => by
          cases encoded with
          | none =>
              exact resolvedCouples_maskedOtsSignFrom parameter table lay tree leafIdx message
                attempts (counter + 1)
          | some encoding =>
              have hreserve := resolvedAdministrative_sequenceFin
                (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
                  (encoding chainIdx))
                (fun _ => ())
                (fun chainIdx => resolvedAdministrative_ensureChainPrefix lay tree leafIdx
                  chainIdx (encoding chainIdx))
              exact (resolvedCouples_of_administrative hreserve).bind fun _ =>
                resolvedCouples_pure parameter table
                  (some (BitVec.ofNat counterBits counter, encoding))

theorem resolvedCouples_maskedOtsSign
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ResolvedCouples parameter table
      (maskedOtsSign parameter lay tree leafIdx message)
      (resolvedOtsSelect parameter lay tree leafIdx message) := by
  exact resolvedCouples_maskedOtsSignFrom parameter table lay tree leafIdx message
    encodingAttemptLimit 0

theorem resolvedCouples_maskedChainValue
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    ResolvedCouples parameter table (maskedChainValue lay tree leafIdx chainIdx digit)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (chainWalk parameter lay tree leafIdx chainIdx 0 digit.val
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))) := by
  intro context fuel cache concreteCache hinvariant
  exact relTriple_runResolvedFromTable_maskedChainValue_clean_or_doomed parameter table lay tree
    leafIdx chainIdx digit context fuel cache concreteCache hinvariant

theorem resolvedCouples_maskedTreeNode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight)
    (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    ResolvedCouples parameter table (maskedTreeNode lay tree level nodeIdx)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          level nodeIdx)) := by
  intro context fuel cache concreteCache hinvariant
  exact relTriple_runResolvedFromTable_maskedTreeNode_clean_or_doomed parameter table lay tree
    level nodeIdx hlevel hspan context fuel cache concreteCache hinvariant

theorem resolvedCouples_maskedTreeRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) :
    ResolvedCouples parameter table (maskedTreeRoot lay tree)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          (layerHeight lay) 0)) := by
  unfold maskedTreeRoot
  apply resolvedCouples_maskedTreeNode parameter table lay tree (layerHeight lay) 0
    (layerHeight_le lay)
  simpa using Nat.pow_le_pow_right (n := 2) (by omega) (layerHeight_le lay)

noncomputable def resolvedLayerMessage
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) : StateT (QueryCache HashSpec) ProbComp Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    simulateQ (randomOracle : QueryImpl HashSpec _)
      (treeNode parameter below (treeIndexAt index below)
        (fun leafIdx chainIdx =>
          truncateHash (table ⟨below, treeIndexAt index below, leafIdx, chainIdx⟩))
        (layerHeight below) 0)
  else
    simulateQ (randomOracle : QueryImpl HashSpec _)
      (ftsKey parameter index (ftsSecret index))

theorem resolvedCouples_maskedLayerMessage
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    ResolvedCouples parameter table (maskedLayerMessage parameter ftsSecret index lay)
      (resolvedLayerMessage parameter table ftsSecret index lay) := by
  unfold maskedLayerMessage resolvedLayerMessage
  split
  · exact resolvedCouples_maskedTreeRoot parameter table _ _
  · exact resolvedCouples_ftsKey parameter table index (ftsSecret index)

noncomputable def resolvedSignLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) : StateT (QueryCache HashSpec) ProbComp
      (Option (Counter × (ChainIndex → Digit))) := do
  let tree := treeIndexAt index lay
  let leafIdx := leafIndexAt index lay
  let message ← resolvedLayerMessage parameter table ftsSecret index lay
  match ← resolvedOtsSelect parameter lay tree leafIdx message with
  | none => pure none
  | some part => pure (some part)

theorem resolvedCouples_maskedSignLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    ResolvedCouples parameter table (maskedSignLayer parameter ftsSecret index lay)
      (resolvedSignLayer parameter table ftsSecret index lay) := by
  unfold maskedSignLayer resolvedSignLayer
  apply (resolvedCouples_maskedLayerMessage parameter table ftsSecret index lay).bind
  intro message
  apply (resolvedCouples_maskedOtsSign parameter table lay (treeIndexAt index lay)
    (leafIndexAt index lay) message).bind
  intro selected
  cases selected with
  | none => exact resolvedCouples_pure parameter table none
  | some part =>
      exact (resolvedCouples_of_administrative
        (resolvedAdministrative_ensureTreePath lay (treeIndexAt index lay)
          (leafIndexAt index lay))).bind fun _ =>
            resolvedCouples_pure parameter table (some part)

noncomputable def resolvedSignAfterDigest
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    StateT (QueryCache HashSpec) ProbComp (Option Signature) := do
  let ftsPath ← simulateQ (randomOracle : QueryImpl HashSpec _)
    (ftsOpen parameter index leaves (ftsSecret index))
  let layers ← sequenceFin fun lay =>
    resolvedSignLayer parameter table ftsSecret index lay
  match traverseOption layers with
  | none => pure none
  | some parts => do
      let revealed ← sequenceFin fun lay =>
        resolvedRevealLayerValues parameter table index lay (parts lay).2
      pure (some
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 })

set_option maxHeartbeats 400000 in
theorem resolvedCouples_maskedSignAfterDigest
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    ResolvedCouples parameter table
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves)
      (resolvedSignAfterDigest parameter table ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest resolvedSignAfterDigest
  apply (resolvedCouples_ftsOpen parameter table index leaves (ftsSecret index)).bind
  intro ftsPath
  apply (resolvedCouples_sequenceFin _ _ fun lay =>
    resolvedCouples_maskedSignLayer parameter table ftsSecret index lay).bind
  intro layers
  cases hparts : traverseOption layers with
  | none => exact resolvedCouples_pure parameter table none
  | some parts =>
      apply (resolvedCouples_sequenceFin _ _ fun lay =>
        resolvedCouples_resolvedRevealLayerValues parameter table index lay
          (parts lay).2).bind
      intro revealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 }
      exact resolvedCouples_pure parameter table (some signature)

noncomputable def resolvedSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    StateT (QueryCache HashSpec) ProbComp (Option Signature) := do
  let secretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  match ← simulateQ romImpl
      (signDigestLoop digestAttemptLimit secretKey message) with
  | none => pure none
  | some (randomness, index, leaves) =>
      resolvedSignAfterDigest parameter table ftsSecret randomness index leaves

set_option maxHeartbeats 400000 in
theorem resolvedCouples_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    ResolvedCouples parameter table (maskedSign parameter root ftsSecret message)
      (resolvedSign parameter root table ftsSecret message) := by
  unfold maskedSign resolvedSign
  let secretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  apply (resolvedCouples_signDigestLoop table secretKey message digestAttemptLimit).bind
  intro selected
  cases selected with
  | none => exact resolvedCouples_pure parameter table none
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      exact resolvedCouples_maskedSignAfterDigest parameter table ftsSecret randomness index
        leaves

theorem reachableResolvedCouples_oracleHash
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : HashInput) (hstable : StableOrdinaryInput parameter input) :
    ReachableResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (oracleHash input))
      (simulateQ (randomOracle : QueryImpl HashSpec _) (oracleHash input)) := by
  simpa only [oracleHash, HasQuery.instOfMonadLift_query, simulateQ_spec_query,
    ordinaryHashImpl] using
    reachableResolvedCouples_splitHashQuery_stable parameter table input hstable

theorem reachableResolvedCouples_tweakableHash
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (domain : HashDomain) (payload : HashInput)
    (hstable : StableOrdinaryInput parameter
      (tweakableHashInput parameter domain payload)) :
    ReachableResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (tweakableHash parameter domain payload))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (tweakableHash parameter domain payload)) := by
  unfold tweakableHash
  rw [simulateQ_bind, simulateQ_bind]
  exact (reachableResolvedCouples_oracleHash parameter table
    (tweakableHashInput parameter domain payload) hstable).bind fun output =>
      reachableResolvedCouples_pure parameter table (truncateHash output)

theorem reachableResolvedCouples_ftsLeafHash
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) (secret : Digest) :
    ReachableResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (ftsLeafHash parameter index tree leafIdx secret))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsLeafHash parameter index tree leafIdx secret)) := by
  unfold ftsLeafHash
  exact reachableResolvedCouples_tweakableHash parameter table (.ftsLeaf index tree leafIdx) _
    (stableOrdinaryInput_tweakableHashInput parameter (.ftsLeaf index tree leafIdx) _
      (by trivial) (by simp) (by simp) (by simp))

theorem reachableResolvedCouples_ftsNode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) :
    ∀ level nodeIdx, level ≤ ftsTreeHeight →
      2 ^ level * (nodeIdx + 1) ≤ 2 ^ ftsTreeHeight →
      ReachableResolvedCouples parameter table
        (simulateQ ordinaryHashImpl
          (ftsNode parameter index tree secret level nodeIdx))
        (simulateQ (randomOracle : QueryImpl HashSpec _)
          (ftsNode parameter index tree secret level nodeIdx))
  | 0, nodeIdx, hlevel, hspan => by
      rw [ftsNode_zero_eq]
      exact reachableResolvedCouples_ftsLeafHash parameter table index tree _ _
  | level + 1, nodeIdx, hlevel, hspan => by
      rw [ftsNode_succ_eq]
      simp only [simulateQ_bind]
      have hleftSpan : 2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1) ≤ 2 ^ level * (2 * (nodeIdx + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ level * 2 * (nodeIdx + 1) := by ring
          _ ≤ 2 ^ ftsTreeHeight := hspan
      have hrightSpan : 2 ^ level * (2 * nodeIdx + 1 + 1) ≤ 2 ^ ftsTreeHeight := by
        rw [pow_succ] at hspan
        calc
          2 ^ level * (2 * nodeIdx + 1 + 1) = 2 ^ level * 2 * (nodeIdx + 1) := by
            ring
          _ ≤ 2 ^ ftsTreeHeight := hspan
      have hinRange : (HashDomain.ftsNode index tree (level + 1) nodeIdx).InRange := by
        show level + 1 < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
        constructor
        · have : ftsTreeHeight < 2 ^ 32 := by norm_num [ftsTreeHeight]
          omega
        · have hnode : nodeIdx < 2 ^ ftsTreeHeight := by
            have hpow : 0 < 2 ^ (level + 1) := Nat.two_pow_pos _
            nlinarith
          have : 2 ^ ftsTreeHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by
            norm_num [ftsTreeHeight])
          omega
      exact (reachableResolvedCouples_ftsNode parameter table index tree secret level
        (2 * nodeIdx) (by omega) hleftSpan).bind fun left =>
          (reachableResolvedCouples_ftsNode parameter table index tree secret level
            (2 * nodeIdx + 1) (by omega) hrightSpan).bind fun right =>
              reachableResolvedCouples_tweakableHash parameter table
                (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)
                (stableOrdinaryInput_tweakableHashInput parameter
                  (.ftsNode index tree (level + 1) nodeIdx) _ hinRange
                  (by simp) (by simp) (by simp))

theorem reachableResolvedCouples_ftsKey
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    ReachableResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (ftsKey parameter index secret))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsKey parameter index secret)) := by
  unfold ftsKey
  rw [simulateQ_bind, simulateQ_bind, simulateQ_ordinaryHashImpl_sequenceFin,
    FtsProbeSimulation.simulateQ_randomOracle_sequenceFin]
  exact (reachableResolvedCouples_sequenceFin
    (fun tree => simulateQ ordinaryHashImpl
      (ftsNode parameter index tree (secret tree) ftsTreeHeight 0))
    (fun tree => simulateQ (randomOracle : QueryImpl HashSpec _)
      (ftsNode parameter index tree (secret tree) ftsTreeHeight 0))
    (fun tree => reachableResolvedCouples_ftsNode parameter table index tree (secret tree)
      ftsTreeHeight 0 le_rfl (by simp))).bind fun roots =>
        reachableResolvedCouples_tweakableHash parameter table (.ftsRoots index)
          (ftsRootsPayload roots)
          (stableOrdinaryInput_tweakableHashInput parameter (.ftsRoots index) _
            (by trivial) (by simp) (by simp) (by simp))

theorem reachableResolvedCouples_ftsOpen
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (leaves : DigestTree → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    ReachableResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (ftsOpen parameter index leaves secret))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (ftsOpen parameter index leaves secret)) := by
  unfold ftsOpen
  rw [simulateQ_ordinaryHashImpl_sequenceFin,
    FtsProbeSimulation.simulateQ_randomOracle_sequenceFin]
  exact reachableResolvedCouples_sequenceFin _ _ fun tree => by
    rw [simulateQ_ordinaryHashImpl_sequenceFin,
      FtsProbeSimulation.simulateQ_randomOracle_sequenceFin]
    exact reachableResolvedCouples_sequenceFin _ _ fun level =>
      reachableResolvedCouples_ftsNode parameter table index tree (secret tree) level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)
        (Nat.le_of_lt level.isLt)
        (FtsProbeSimulation.ftsOpen_node_bound (leaves (ftsIndexOf tree)) level)

theorem reachableResolvedCouples_encode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    ReachableResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (encode parameter lay tree leafIdx message counter))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (encode parameter lay tree leafIdx message counter)) := by
  unfold encode
  rw [simulateQ_bind, simulateQ_bind]
  exact (reachableResolvedCouples_tweakableHash parameter table (.encoding lay tree leafIdx) _
    (stableOrdinaryInput_tweakableHashInput parameter (.encoding lay tree leafIdx) _
      (by trivial) (by simp) (by simp) (by simp))).bind fun digest =>
        reachableResolvedCouples_pure parameter table (TargetSum.decodeDigest digest)

theorem reachableResolvedCouples_messageDigest
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (root : Digest) (message : Message) (randomness : Randomness) :
    ReachableResolvedCouples parameter table
      (simulateQ ordinaryHashImpl (messageDigest parameter root message randomness))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (messageDigest parameter root message randomness)) := by
  unfold messageDigest
  rw [simulateQ_bind, simulateQ_bind]
  exact (reachableResolvedCouples_oracleHash parameter table
    (tweakableHashInput parameter .message
      (messageDigestPayload root message randomness))
    (stableOrdinaryInput_tweakableHashInput parameter .message _
      (by trivial) (by simp) (by simp) (by simp))).bind fun output =>
        reachableResolvedCouples_pure parameter table (truncateMessageDigest output)

theorem reachableResolvedCouples_signAttempt
    (table : OtsSecretIndex → HashOutput) (secretKey : SecretKey)
    (message : Message) (randomness : Randomness) :
    ReachableResolvedCouples secretKey.parameter table
      (simulateQ ordinaryHashImpl (signAttempt secretKey message randomness))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)) := by
  unfold signAttempt
  simp only [simulateQ_bind]
  exact (reachableResolvedCouples_messageDigest secretKey.parameter table secretKey.root message
    randomness).bind fun digest => by
      split <;> exact reachableResolvedCouples_pure secretKey.parameter table _

theorem reachableResolvedCouples_signDigestLoop
    (table : OtsSecretIndex → HashOutput) (secretKey : SecretKey)
    (message : Message) : ∀ attempts,
    ReachableResolvedCouples secretKey.parameter table
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message))
      (simulateQ romImpl (signDigestLoop attempts secretKey message))
  | 0 => by
      rw [signDigestLoop, simulateQ_pure, simulateQ_pure]
      exact reachableResolvedCouples_pure secretKey.parameter table none
  | attempts + 1 => by
      rw [signDigestLoop, simulateQ_bind, simulateQ_bind]
      have hrandomness : ReachableResolvedCouples secretKey.parameter table
          (simulateQ ordinaryRomImpl (liftM sampleRandomness))
          (simulateQ romImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, romImpl, QueryImpl.simulateQ_add_liftM_left,
          QueryImpl.simulateQ_add_liftM_left]
        exact reachableResolvedCouples_simulateQ splitUniformImpl (unifFwdImpl HashSpec)
          (reachableResolvedCouples_splitUniform secretKey.parameter table) sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind, simulateQ_bind]
        have hattempt : ReachableResolvedCouples secretKey.parameter table
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))))
            (simulateQ romImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, romImpl, QueryImpl.simulateQ_add_liftM_right,
            QueryImpl.simulateQ_add_liftM_right]
          exact reachableResolvedCouples_signAttempt table secretKey message randomness
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none => exact reachableResolvedCouples_signDigestLoop table secretKey message attempts
          | some selected => exact reachableResolvedCouples_pure secretKey.parameter table _

theorem reachableResolvedCouples_maskedOtsSignFrom
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter,
      ReachableResolvedCouples parameter table
        (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
        (resolvedOtsSelectFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom, resolvedOtsSelectFrom]
      exact reachableResolvedCouples_pure parameter table none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom, resolvedOtsSelectFrom]
      exact (reachableResolvedCouples_encode parameter table lay tree leafIdx message
        (BitVec.ofNat counterBits counter)).bind fun encoded => by
          cases encoded with
          | none =>
              exact reachableResolvedCouples_maskedOtsSignFrom parameter table lay tree leafIdx
                message attempts (counter + 1)
          | some encoding =>
              have hreserve := resolvedAdministrative_sequenceFin
                (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx
                  (encoding chainIdx))
                (fun _ => ())
                (fun chainIdx => resolvedAdministrative_ensureChainPrefix lay tree leafIdx
                  chainIdx (encoding chainIdx))
              have hreservePublished := resolvedPreservesPublished_sequenceFin
                (fun chainIdx => ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx))
                (fun chainIdx => resolvedPreservesPublished_ensureChainPrefix lay tree leafIdx
                  chainIdx (encoding chainIdx))
              exact (reachableResolvedCouples_of_administrative hreserve
                hreservePublished).bind fun _ =>
                reachableResolvedCouples_pure parameter table
                  (some (BitVec.ofNat counterBits counter, encoding))

theorem reachableResolvedCouples_maskedOtsSign
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ReachableResolvedCouples parameter table
      (maskedOtsSign parameter lay tree leafIdx message)
      (resolvedOtsSelect parameter lay tree leafIdx message) := by
  exact reachableResolvedCouples_maskedOtsSignFrom parameter table lay tree leafIdx message
    encodingAttemptLimit 0

theorem reachableResolvedCouples_revealPublishedChainValue
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    ReachableResolvedCouples parameter table
      (revealPublishedCoordinate
        (chainValueCoordinate lay tree leafIdx chainIdx digit))
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (chainWalk parameter lay tree leafIdx chainIdx 0 digit.val
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))) := by
  unfold revealPublishedCoordinate chainValueCoordinate
  split
  · have hbase := (reachableResolvedCouples_revealChainStart parameter table
      ⟨lay, tree, leafIdx, chainIdx⟩).publishAfter
        (.chainStart lay tree leafIdx chainIdx) (by
          intro context fuel cache result hresult
          exact value_ne_none_of_mem_runResolvedFromTable_revealCoordinate context fuel table
            (.chainStart lay tree leafIdx chainIdx) cache result (by
              simpa [revealChainStart] using hresult))
    simpa [revealChainStart, chainWalk, ‹digit.val = 0›] using hbase
  · let step : ChainStep := ⟨digit.val - 1, by
      have := digit.isLt
      omega⟩
    have hwalk : resolvedPositionComputation parameter table
        (.chain lay tree leafIdx chainIdx step) =
        chainWalk parameter lay tree leafIdx chainIdx 0 digit.val
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) := by
      simp [resolvedPositionComputation, step]
      have hpos : 0 < digit.val := Nat.pos_of_ne_zero ‹digit.val ≠ 0›
      congr 1
      omega
    rw [← hwalk]
    have hbase := (reachableResolvedCouples_revealResolvablePosition parameter table
      (.chain lay tree leafIdx chainIdx step) (by simp [ResolvableOtsPosition])).publishAfter
        (.position (.chain lay tree leafIdx chainIdx step)) (by
          intro context fuel cache result hresult
          exact value_ne_none_of_mem_runResolvedFromTable_revealCoordinate context fuel table
            (.position (.chain lay tree leafIdx chainIdx step)) cache result (by
              simpa [revealPosition] using hresult))
    simpa [revealPosition, step] using hbase

theorem reachableResolvedCouples_revealPublishedTreeNode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight)
    (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    ReachableResolvedCouples parameter table
      (match level with
        | 0 => revealPublishedCoordinate (.position (.leaf lay tree (leafOfNat nodeIdx)))
        | current + 1 =>
            if hcurrent : current < maxLayerHeight then
              revealPublishedCoordinate (.position
                (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)))
            else pure 0)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          level nodeIdx)) := by
  cases level with
  | zero =>
      have hbase := (reachableResolvedCouples_revealResolvablePosition parameter table
        (.leaf lay tree (leafOfNat nodeIdx)) (by simp [ResolvableOtsPosition])).publishAfter
          (.position (.leaf lay tree (leafOfNat nodeIdx))) (by
            intro context fuel cache result hresult
            exact value_ne_none_of_mem_runResolvedFromTable_revealCoordinate context fuel table
              (.position (.leaf lay tree (leafOfNat nodeIdx))) cache result (by
                simpa [revealPosition] using hresult))
      simpa [revealPublishedCoordinate, revealPosition, resolvedPositionComputation,
        treeNode_zero_eq] using hbase
  | succ current =>
      have hcurrent : current < maxLayerHeight := by omega
      simp only [hcurrent, ↓reduceDIte]
      have hnodeLt : nodeIdx < 2 ^ maxLayerHeight := by
        have hpow : 0 < 2 ^ (current + 1) := pow_pos (by omega) _
        nlinarith
      have hnodeVal : (leafOfNat nodeIdx).val = nodeIdx := by
        simp [leafOfNat, Nat.mod_eq_of_lt hnodeLt]
      have hresolvable : ResolvableOtsPosition
          (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) := by
        simp [ResolvableOtsPosition, hnodeVal]
        exact hspan
      have hbase := (reachableResolvedCouples_revealResolvablePosition parameter table
        (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) hresolvable).publishAfter
          (.position (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx))) (by
            intro context fuel cache result hresult
            exact value_ne_none_of_mem_runResolvedFromTable_revealCoordinate context fuel table
              (.position (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx))) cache result
                (by simpa [revealPosition] using hresult))
      simpa [revealPublishedCoordinate, revealPosition, resolvedPositionComputation,
        hnodeVal] using hbase

theorem reachableResolvedCouples_revealLayerPathNode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (lay : Layer) (level : Fin maxLayerHeight) :
    ReachableResolvedCouples parameter table
      (if level.val < layerHeight lay then
        match level.val with
        | 0 => revealPublishedCoordinate (.position (.leaf lay (treeIndexAt index lay)
            (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | current + 1 =>
            if hcurrent : current < maxLayerHeight then
              revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                ⟨current, hcurrent⟩ (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            else pure 0
      else pure 0)
      (if level.val < layerHeight lay then
        simulateQ (randomOracle : QueryImpl HashSpec _)
          (treeNode parameter lay (treeIndexAt index lay)
            (fun sibling chainIdx =>
              truncateHash (table ⟨lay, treeIndexAt index lay, sibling, chainIdx⟩))
            level.val
            (Nat.xor ((leafIndexAt index lay).val / 2 ^ level.val) 1))
      else pure 0) := by
  by_cases hinLayer : level.val < layerHeight lay
  · rw [if_pos hinLayer, if_pos hinLayer]
    cases hvalue : level.val with
    | zero =>
        simpa [hvalue] using
          reachableResolvedCouples_revealPublishedTreeNode parameter table lay
            (treeIndexAt index lay) 0
            (Nat.xor (leafIndexAt index lay).val 1) (by omega)
            (by
              simpa using (FtsProbeSimulation.sibling_node_bound maxLayerHeight
                (leafIndexAt index lay).val 0 (by omega) (leafIndexAt index lay).isLt))
    | succ current =>
        have hcurrent : current < maxLayerHeight := by
          have := level.isLt
          omega
        simpa [hvalue, hcurrent] using
          reachableResolvedCouples_revealPublishedTreeNode parameter table lay
            (treeIndexAt index lay) (current + 1)
            (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1)
            (by omega)
            (FtsProbeSimulation.sibling_node_bound maxLayerHeight
              (leafIndexAt index lay).val (current + 1) (by omega)
              (leafIndexAt index lay).isLt)
  · rw [if_neg hinLayer, if_neg hinLayer]
    exact reachableResolvedCouples_pure parameter table 0

set_option maxHeartbeats 400000 in
theorem reachableResolvedCouples_revealLayerValues
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    ReachableResolvedCouples parameter table (revealLayerValues index lay encoding)
      (do
        let tree := treeIndexAt index lay
        let leafIdx := leafIndexAt index lay
        let values ← sequenceFin fun chainIdx =>
          simulateQ (randomOracle : QueryImpl HashSpec _)
            (chainWalk parameter lay tree leafIdx chainIdx 0 (encoding chainIdx).val
              (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))
        let path ← sequenceFin fun level : Fin maxLayerHeight =>
          if level.val < layerHeight lay then
            simulateQ (randomOracle : QueryImpl HashSpec _)
              (treeNode parameter lay tree
                (fun sibling chainIdx =>
                  truncateHash (table ⟨lay, tree, sibling, chainIdx⟩))
                level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1))
          else
            pure 0
        pure (values, path)) := by
  unfold revealLayerValues
  apply (reachableResolvedCouples_sequenceFin _ _ fun chainIdx =>
    reachableResolvedCouples_revealPublishedChainValue parameter table lay
      (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx)).bind
  intro values
  apply (reachableResolvedCouples_sequenceFin _ _ fun level =>
    reachableResolvedCouples_revealLayerPathNode parameter table index lay level).bind
  intro path
  exact reachableResolvedCouples_pure parameter table (values, path)

theorem reachableResolvedCouples_resolvedRevealLayerValues
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    ReachableResolvedCouples parameter table (revealLayerValues index lay encoding)
      (resolvedRevealLayerValues parameter table index lay encoding) := by
  unfold resolvedRevealLayerValues
  exact reachableResolvedCouples_revealLayerValues parameter table index lay encoding

theorem reachableResolvedCouples_maskedChainValue
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    ReachableResolvedCouples parameter table (maskedChainValue lay tree leafIdx chainIdx digit)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (chainWalk parameter lay tree leafIdx chainIdx 0 digit.val
          (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))) := by
  unfold maskedChainValue
  by_cases hzero : digit.val = 0
  · rw [dif_pos hzero]
    have hbase := (reachableResolvedCouples_of_administrative
      (resolvedAdministrative_ensureChainPrefix lay tree leafIdx chainIdx digit)
      (resolvedPreservesPublished_ensureChainPrefix lay tree leafIdx chainIdx digit)).bind fun _ =>
        reachableResolvedCouples_revealChainStart parameter table
          ⟨lay, tree, leafIdx, chainIdx⟩
    simpa [hzero, chainWalk] using hbase
  · rw [dif_neg hzero]
    let step : ChainStep := ⟨digit.val - 1, by
      have := digit.isLt
      omega⟩
    have hsteps : step.val + 1 = digit.val := by
      simp [step]
      omega
    have hbase := (reachableResolvedCouples_of_administrative
      (resolvedAdministrative_ensureChainPrefix lay tree leafIdx chainIdx digit)
      (resolvedPreservesPublished_ensureChainPrefix lay tree leafIdx chainIdx digit)).bind fun _ =>
        reachableResolvedCouples_revealResolvablePosition parameter table
          (.chain lay tree leafIdx chainIdx step) (by simp [ResolvableOtsPosition])
    simpa [resolvedPositionComputation, step, hsteps] using hbase

theorem reachableResolvedCouples_maskedTreeNode
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight)
    (hspan : 2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight) :
    ReachableResolvedCouples parameter table (maskedTreeNode lay tree level nodeIdx)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          level nodeIdx)) := by
  unfold maskedTreeNode
  cases level with
  | zero =>
      have hbase := (reachableResolvedCouples_of_administrative
        (resolvedAdministrative_ensureTreeNode lay tree 0 nodeIdx)
        (resolvedPreservesPublished_ensureTreeNode lay tree 0 nodeIdx)).bind fun _ =>
          reachableResolvedCouples_revealResolvablePosition parameter table
            (.leaf lay tree (leafOfNat nodeIdx)) (by simp [ResolvableOtsPosition])
      simpa [resolvedPositionComputation, treeNode_zero_eq] using hbase
  | succ current =>
      have hcurrent : current < maxLayerHeight := by omega
      simp only [hcurrent, ↓reduceDIte]
      have hnodeLt : nodeIdx < 2 ^ maxLayerHeight := by
        have hpow : 0 < 2 ^ (current + 1) := pow_pos (by omega) _
        nlinarith
      have hnodeVal : (leafOfNat nodeIdx).val = nodeIdx := by
        simp [leafOfNat, Nat.mod_eq_of_lt hnodeLt]
      have hresolvable : ResolvableOtsPosition
          (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) := by
        simp [ResolvableOtsPosition, hnodeVal]
        exact hspan
      have hbase := (reachableResolvedCouples_of_administrative
        (resolvedAdministrative_ensureTreeNode lay tree (current + 1) nodeIdx)
        (resolvedPreservesPublished_ensureTreeNode lay tree (current + 1) nodeIdx)).bind fun _ =>
          reachableResolvedCouples_revealResolvablePosition parameter table
            (.node lay tree ⟨current, hcurrent⟩ (leafOfNat nodeIdx)) hresolvable
      simpa [resolvedPositionComputation, hnodeVal] using hbase

theorem reachableResolvedCouples_maskedTreeRoot
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (lay : Layer) (tree : TreeIndex) :
    ReachableResolvedCouples parameter table (maskedTreeRoot lay tree)
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeNode parameter lay tree
          (fun leafIdx chainIdx =>
            truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
          (layerHeight lay) 0)) := by
  unfold maskedTreeRoot
  apply reachableResolvedCouples_maskedTreeNode parameter table lay tree (layerHeight lay) 0
    (layerHeight_le lay)
  simpa using Nat.pow_le_pow_right (n := 2) (by omega) (layerHeight_le lay)

theorem reachableResolvedCouples_maskedLayerMessage
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    ReachableResolvedCouples parameter table (maskedLayerMessage parameter ftsSecret index lay)
      (resolvedLayerMessage parameter table ftsSecret index lay) := by
  unfold maskedLayerMessage resolvedLayerMessage
  split
  · exact reachableResolvedCouples_maskedTreeRoot parameter table _ _
  · exact reachableResolvedCouples_ftsKey parameter table index (ftsSecret index)

theorem reachableResolvedCouples_maskedSignLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    ReachableResolvedCouples parameter table (maskedSignLayer parameter ftsSecret index lay)
      (resolvedSignLayer parameter table ftsSecret index lay) := by
  unfold maskedSignLayer resolvedSignLayer
  apply (reachableResolvedCouples_maskedLayerMessage parameter table ftsSecret index lay).bind
  intro message
  apply (reachableResolvedCouples_maskedOtsSign parameter table lay (treeIndexAt index lay)
    (leafIndexAt index lay) message).bind
  intro selected
  cases selected with
  | none => exact reachableResolvedCouples_pure parameter table none
  | some part =>
      exact (reachableResolvedCouples_of_administrative
        (resolvedAdministrative_ensureTreePath lay (treeIndexAt index lay)
          (leafIndexAt index lay))
        (resolvedPreservesPublished_ensureTreePath lay (treeIndexAt index lay)
          (leafIndexAt index lay))).bind fun _ =>
            reachableResolvedCouples_pure parameter table (some part)

set_option maxHeartbeats 400000 in
theorem reachableResolvedCouples_maskedSignAfterDigest
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    ReachableResolvedCouples parameter table
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves)
      (resolvedSignAfterDigest parameter table ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest resolvedSignAfterDigest
  apply (reachableResolvedCouples_ftsOpen parameter table index leaves (ftsSecret index)).bind
  intro ftsPath
  apply (reachableResolvedCouples_sequenceFin _ _ fun lay =>
    reachableResolvedCouples_maskedSignLayer parameter table ftsSecret index lay).bind
  intro layers
  cases hparts : traverseOption layers with
  | none => exact reachableResolvedCouples_pure parameter table none
  | some parts =>
      apply (reachableResolvedCouples_sequenceFin _ _ fun lay =>
        reachableResolvedCouples_resolvedRevealLayerValues parameter table index lay
          (parts lay).2).bind
      intro revealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 }
      exact reachableResolvedCouples_pure parameter table (some signature)

set_option maxHeartbeats 400000 in
theorem reachableResolvedCouples_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    ReachableResolvedCouples parameter table (maskedSign parameter root ftsSecret message)
      (resolvedSign parameter root table ftsSecret message) := by
  unfold maskedSign resolvedSign
  let secretKey : SecretKey :=
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  apply (reachableResolvedCouples_signDigestLoop table secretKey message digestAttemptLimit).bind
  intro selected
  cases selected with
  | none => exact reachableResolvedCouples_pure parameter table none
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      exact reachableResolvedCouples_maskedSignAfterDigest parameter table ftsSecret randomness
        index leaves

def DeferredFreshOn (coordinates : List Coordinate) (context : DeferredContext) : Prop :=
  ∀ position : Position, Coordinate.position position ∈ coordinates →
    context.values position = none

theorem finalizeResolvedCoordinates_projects_to_clean
    (coordinates : List Coordinate) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput)
    (hnodup : coordinates.Nodup) (hfresh : DeferredFreshOn coordinates context) :
    (fun result => result.map fun finalContext => (finalContext.state, table)) <$>
        finalizeResolvedCoordinates coordinates context table =
      finalizeCleanFromTable coordinates context.state table := by
  induction coordinates generalizing context with
  | nil => simp [finalizeResolvedCoordinates, finalizeCleanFromTable]
  | cons coordinate remaining ih =>
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      cases hstate : context.state.values coordinate with
      | some output =>
          rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
          simp only [hstate]
          apply ih { context with state := context.state.clearPending coordinate }
            htailNodup
          intro position hmem
          exact hfresh position (List.mem_cons_of_mem coordinate hmem)
      | none =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              have hstate' : context.state.values index.coordinate = none := by
                simpa [index, OtsSecretIndex.coordinate] using hstate
              rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
              simp only [hstate]
              rw [resolveDeferredChainStart_of_missing table index context hstate']
              by_cases hhit : context.state.hitAt
                  (.chainStart lay tree leafIdx chainIdx) (table index)
              · simp [index, OtsSecretIndex.coordinate, hhit]
              · simp only [index, OtsSecretIndex.coordinate, hhit, ↓reduceIte,
                  map_eq_bind_pure_comp, pure_bind]
                rw [clearPending_complete_self]
                simpa only [map_eq_bind_pure_comp] using ih
                  { state := context.state.complete (.chainStart lay tree leafIdx chainIdx)
                      (table index)
                    values := context.values }
                  htailNodup (by
                    intro position hmem
                    exact hfresh position (List.mem_cons_of_mem _ hmem))
          | position position =>
              have hvalue : context.values position = none :=
                hfresh position (by simp)
              rw [finalizeResolvedCoordinates, finalizeCleanFromTable.eq_def]
              simp only [hstate]
              rw [resolveDeferredPositionValue_fresh position context hstate hvalue]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply bind_congr
              intro output
              by_cases hhit : context.state.hitAt (.position position) output
              · simp [hhit]
              · simp only [hhit, ↓reduceIte]
                simp only [pure_bind]
                rw [clearPending_complete_self]
                simpa only [map_eq_bind_pure_comp] using ih
                  { state := context.state.complete (.position position) output
                    values := context.values.install position output }
                  htailNodup (by
                    intro other hmem
                    have hne : other ≠ position := by
                      intro heq
                      subst other
                      exact hnotMem hmem
                    simp [DeferredStructuralValues.install, hne,
                      hfresh other (List.mem_cons_of_mem _ hmem)])

theorem finalizeResolvedCoordinates_empty_projects_to_clean
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput) (hnodup : coordinates.Nodup) :
    (fun result => result.map fun finalContext => (finalContext.state, table)) <$>
        finalizeResolvedCoordinates coordinates
          { state := state, values := emptyDeferredStructuralValues } table =
      finalizeCleanFromTable coordinates state table := by
  apply finalizeResolvedCoordinates_projects_to_clean coordinates
    { state := state, values := emptyDeferredStructuralValues } table hnodup
  intro position hmem
  rfl

theorem finalizeResolvedCoordinates_empty_finset_projects_to_clean
    (coordinates : Finset Coordinate) (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput) :
    (fun result => result.map fun finalContext => (finalContext.state, table)) <$>
        finalizeResolvedCoordinates coordinates.toList
          { state := state, values := emptyDeferredStructuralValues } table =
      finalizeCleanFromTable coordinates.toList state table :=
  finalizeResolvedCoordinates_empty_projects_to_clean coordinates.toList state table
    coordinates.nodup_toList

noncomputable def finishResolvedRun :
    Option (ResolvedRunResult alpha) → ProbComp (Option (ResolvedRunResult alpha)) := by
  classical
  intro input
  cases input with
  | none => exact pure none
  | some result =>
      exact if DeferredCompletable result.table result.context then do
          let finalized ← finalizeResolvedCoordinates result.context.state.coordinates.toList
            result.context result.table
          match finalized with
          | none => pure none
          | some context => pure (some ⟨context, result.remaining, result.value, result.table⟩)
        else pure none

theorem finishResolvedRun_of_not_deferredCompletable
    (result : ResolvedRunResult alpha)
    (hdoomed : ¬DeferredCompletable result.table result.context) :
    finishResolvedRun (some result) = pure none := by
  simp [finishResolvedRun, hdoomed]

def projectResolvedRunResult :
    Option (ResolvedRunResult alpha) → Option (CleanRunResult alpha)
  | none => none
  | some result => some ⟨result.context.state, result.remaining, result.value, result.table⟩

theorem finishResolvedRun_empty_projects_to_clean
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : alpha) (table : OtsSecretIndex → HashOutput)
    (hcompletable : DeferredCompletable table
      { state := state, values := emptyDeferredStructuralValues }) :
    projectResolvedRunResult <$>
        finishResolvedRun (some ⟨
          { state := state, values := emptyDeferredStructuralValues },
          fuel, value, table⟩) =
      finishCleanRunFromTable (some ⟨state, fuel, value, table⟩) := by
  simp only [finishResolvedRun, hcompletable, ↓reduceIte, finishCleanRunFromTable]
  rw [← finalizeResolvedCoordinates_empty_finset_projects_to_clean
    state.coordinates state table]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro finalized
  cases finalized <;> simp [projectResolvedRunResult]

end SphincsSecurity.Concrete.OtsProbeSimulation
