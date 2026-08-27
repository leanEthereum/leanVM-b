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
    (invariant : DeferredContext → QueryCache HashSpec → Prop) :
    Option DeferredResolution → Digest × QueryCache HashSpec → Prop
  | none, _ => True
  | some resolved, (value, cache) =>
      value = truncateHash resolved.output ∧ invariant resolved.toDeferredContext cache

theorem relTriple_resolveDeferredChainStart
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (cache : QueryCache HashSpec)
    (invariant : DeferredContext → QueryCache HashSpec → Prop)
    (hagrees : StartTableAgrees context.state table)
    (hpreserves : ∀ result,
      resolveDeferredChainStart table index context = some result →
      invariant result.toDeferredContext cache) :
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
    (invariant : DeferredContext → QueryCache HashSpec → Prop)
    (hagrees : StartTableAgrees context.state table)
    (hstartPreserves : ∀ result,
      resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context = some result →
      invariant result.toDeferredContext cache)
    (hinput : ∀ (step : ChainStep) middleContext middleCache previousOutput,
      invariant middleContext middleCache →
      ResolveInputAgrees (.chain lay tree leafIdx chainIdx step) middleContext
        (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step)
          (digestBytes (truncateHash previousOutput))) middleCache)
    (hqueryPreserves : ∀ (step : ChainStep) middleContext middleCache previousOutput
        result output finalCache,
      invariant middleContext middleCache →
      ResolveQueryRel
          (tweakableHashInput parameter (.chain lay tree leafIdx chainIdx step)
            (digestBytes (truncateHash previousOutput))) middleCache
          (some result) (output, finalCache) →
      invariant result.toDeferredContext finalCache) :
    ∀ steps hsteps,
      RelTriple
        (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps hsteps context)
        ((simulateQ (randomOracle : QueryImpl HashSpec _)
          (chainWalk parameter lay tree leafIdx chainIdx 0 steps
            (truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)))).run cache)
        (ResolveChainRel invariant)
  | 0, hsteps => by
      simpa [resolveDeferredChainPrefix, chainWalk] using
        relTriple_resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩
          context cache invariant hagrees hstartPreserves
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
            hinput step previous.toDeferredContext middleCache previous.output hinvariant
          have hquery := relTriple_resolveDeferredPositionValue_of_inputAgrees
            (.chain lay tree leafIdx chainIdx step) previous.toDeferredContext input middleCache
              hagreesInput
          have hbound : RelTriple
              (resolveDeferredPositionValue (.chain lay tree leafIdx chainIdx step)
                previous.toDeferredContext >>= fun resolved => pure resolved)
              ((randomOracle input).run middleCache >>= fun result =>
                pure (truncateHash result.1, result.2))
              (ResolveChainRel invariant) := by
            apply relTriple_bind hquery
            intro resolved queryResult hrelation
            apply relTriple_pure_pure
            cases resolved with
            | none => trivial
            | some resolved =>
                rcases queryResult with ⟨queryOutput, finalCache⟩
                refine ⟨?_, hqueryPreserves step previous.toDeferredContext middleCache
                  previous.output resolved queryOutput finalCache hinvariant hrelation⟩
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
            | .position position => resolveDeferredPosition table position context
          match resolved with
          | none => pure none
          | some resolved =>
              recursivelyRun resolved.output
                { state := resolved.state.materialize coordinate resolved.output
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
        | .position position => resolveDeferredPosition table position context
      match resolved with
      | none => pure none
      | some resolved =>
          runResolvedFromTable
            { state := resolved.state.materialize coordinate resolved.output
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
                  { state := resolved.state.materialize _ resolved.output
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
        | .position position => resolveDeferredPosition table position context
      match resolved with
      | none => pure none
      | some resolved =>
          pure (some ⟨
            { state := resolved.state.materialize coordinate resolved.output
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
      let resolved ← resolveDeferredPosition table position context
      match resolved with
      | none => pure none
      | some resolved =>
          pure (some ⟨
            { state := resolved.state.materialize (.position position) resolved.output
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
        { state := (context.state.clearPending index.coordinate).materialize
            index.coordinate (table index)
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
          { state := (reservedContext.state.clearPending
                (.chainStart lay tree leafIdx chainIdx)).materialize
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
              { state := resolved.state.materialize
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
  exact runResolvedFromTable_revealPosition reservedContext fuel table
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
    Option (ResolvedRunResult alpha) → ProbComp (Option (ResolvedRunResult alpha))
  | none => pure none
  | some result => do
      let finalized ← finalizeResolvedCoordinates result.context.state.coordinates.toList
        result.context result.table
      match finalized with
      | none => pure none
      | some context => pure (some ⟨context, result.remaining, result.value, result.table⟩)

def projectResolvedRunResult :
    Option (ResolvedRunResult alpha) → Option (CleanRunResult alpha)
  | none => none
  | some result => some ⟨result.context.state, result.remaining, result.value, result.table⟩

theorem finishResolvedRun_empty_projects_to_clean
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : alpha) (table : OtsSecretIndex → HashOutput) :
    projectResolvedRunResult <$>
        finishResolvedRun (some ⟨
          { state := state, values := emptyDeferredStructuralValues },
          fuel, value, table⟩) =
      finishCleanRunFromTable (some ⟨state, fuel, value, table⟩) := by
  simp only [finishResolvedRun, finishCleanRunFromTable]
  rw [← finalizeResolvedCoordinates_empty_finset_projects_to_clean
    state.coordinates state table]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro finalized
  cases finalized <;> simp [projectResolvedRunResult]

end SphincsSecurity.Concrete.OtsProbeSimulation
