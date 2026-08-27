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
  have hcacheEq := hinvariant.2.2.2.2.eq_of_stable hinvariant.2.2.2.1 input hstable
  rw [splitHashQuery_run_eq]
  cases hlookup : cache (.ordinary input) with
  | some output =>
      have hordinary : ordinaryQueryCache cache input = some output := hlookup
      have hconcrete : concreteCache input = some output := by
        rw [← hcacheEq]
        exact hordinary
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hconcrete]
      simp [runResolvedFromTable, ResolvedOrdinaryRunRel]
      exact hinvariant
  | none =>
      have hordinary : ordinaryQueryCache cache input = none := hlookup
      have hconcrete : concreteCache input = none := by
        rw [← hcacheEq]
        exact hordinary
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hconcrete,
        LazyRevealProbe.hashOutputQuery,
        runResolvedFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput heq
      subst rightOutput
      apply relTriple_pure_pure
      refine ⟨rfl, rfl, ?_⟩
      rw [ordinaryQueryCache_update]
      exact hinvariant.of_stable_cacheQuery input leftOutput hstable

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
  simp only [StateT.run_pure, runResolvedFromTable]
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
