import SphincsSecurity.Proof.OtsProbeResolvedCacheSupport
import SphincsSecurity.Proof.OtsProbeEncodingPotentialHash
import SphincsSecurity.Proof.EncodingCacheExtension

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ResolvedPreservesCachedInput (input : HashInput)
    (computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel table cache result,
    some result ∈ support (runResolvedFromTable context fuel table (computation.run cache)) →
    ∀ output, cache (.ordinary input) = some output → result.value.2 (.ordinary input) = some output

theorem ResolvedPreservesCachedInput.pure (input : HashInput) (value : α) :
    ResolvedPreservesCachedInput input (pure value) := by
  intro context fuel table cache result hresult output hcached
  simp only [StateT.run_pure, runResolvedFromTable, construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
  subst result
  exact hcached

theorem ResolvedPreservesCachedInput.bind {input : HashInput}
    {left : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : ResolvedPreservesCachedInput input left) (hnext : ∀ value, ResolvedPreservesCachedInput input (next value)) :
    ResolvedPreservesCachedInput input (left >>= next) := by
  intro context fuel table cache result hresult output hcached
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middleOption, hmiddle, hrest⟩ := hresult
  cases middleOption with
  | none => simp at hrest
  | some middle =>
      exact hnext middle.value.1 middle.context middle.remaining middle.table middle.value.2 result hrest output
        (hleft context fuel table cache middle hmiddle output hcached)

theorem resolvedPreservesCachedInput_lift (input : HashInput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ResolvedPreservesCachedInput input (liftM computation) := by
  intro context fuel table cache result hresult output hcached
  have hsource := mem_support_of_runResolvedFromTable _ context fuel table result hresult
  change result.value ∈ support (computation >>= fun value => pure (value, cache)) at hsource
  rw [mem_support_bind_iff] at hsource
  obtain ⟨value, _, heq⟩ := hsource
  simp only [mem_support_pure_iff] at heq
  rw [heq]
  exact hcached

theorem resolvedPreservesCachedInput_modify (input : HashInput) (update : SplitHashCache → SplitHashCache)
    (hupdate : ∀ cache output, cache (.ordinary input) = some output → update cache (.ordinary input) = some output) :
    ResolvedPreservesCachedInput input (modify update) := by
  intro context fuel table cache result hresult output hcached
  change some result ∈ support (pure (some (⟨context, fuel, ((), update cache), table⟩ : ResolvedRunResult _))) at hresult
  simp only [mem_support_pure_iff, Option.some.injEq] at hresult
  subst result
  exact hupdate cache output hcached

theorem resolvedPreservesCachedInput_splitHashQuery (input : HashInput) (key : SplitHashKey) :
    ResolvedPreservesCachedInput input (splitHashQuery key) := by
  intro context fuel table cache result hresult output hcached
  have hsource := mem_support_of_runResolvedFromTable _ context fuel table result hresult
  rw [splitHashQuery_run_eq] at hsource
  cases hlookup : cache key with
  | some answer =>
      simp only [hlookup, mem_support_pure_iff] at hsource
      rw [hsource]
      exact hcached
  | none =>
      simp only [hlookup, mem_support_bind_iff, mem_support_pure_iff] at hsource
      obtain ⟨answer, _, heq⟩ := hsource
      rw [heq]
      by_cases hkey : SplitHashKey.ordinary input = key
      · rw [hkey, hlookup] at hcached
        cases hcached
      · exact (Function.update_of_ne hkey _ _).trans hcached

theorem resolvedPreservesCachedInput_peekTableInput (input : HashInput) (parameter : PublicParameter) (coordinate : Coordinate) :
    ResolvedPreservesCachedInput input (peekTableInput parameter coordinate) := by
  intro context fuel table cache result hresult output hcached
  rw [runResolvedFromTable_peekTableInput_eq_pure] at hresult
  simp only [mem_support_pure_iff, Option.some.injEq] at hresult
  subst result
  exact hcached

theorem resolvedPreservesCachedInput_revealCoordinateOutput (input : HashInput) (coordinate : Coordinate) :
    ResolvedPreservesCachedInput input (revealCoordinateOutput coordinate) := by
  unfold revealCoordinateOutput
  apply (resolvedPreservesCachedInput_lift input _).bind
  intro output
  exact (resolvedPreservesCachedInput_modify input _ (fun cache answer hcached => by
    simpa only [Function.update_of_ne (show SplitHashKey.ordinary input ≠ .hidden coordinate by simp)] using hcached)).bind
      fun _ => ResolvedPreservesCachedInput.pure input _

theorem resolvedPreservesCachedEncoding_resolveKnownInput
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest) (tracked : HashInput)
    (htracked : tracked ∈ encodingRetryInputs encodingParameter position message) (coordinate : Coordinate) (input : HashInput) :
    ResolvedPreservesCachedInput tracked (resolveKnownInput parameter coordinate input) := by
  by_cases heq : input = tracked
  · subst input
    intro context fuel table cache result hresult output hcached
    rw [runResolvedFromTable_resolveKnownInput_of_miss parameter coordinate tracked context fuel table cache
      (purePeekTableInput_ne_of_mem_encodingRetryInputs encodingParameter parameter position message context.state coordinate tracked htracked)] at hresult
    exact resolvedPreservesCachedInput_splitHashQuery tracked (.ordinary tracked) context fuel table cache result hresult output hcached
  · unfold resolveKnownInput
    apply (resolvedPreservesCachedInput_peekTableInput tracked parameter coordinate).bind
    intro known
    cases known with
    | none => exact resolvedPreservesCachedInput_splitHashQuery tracked _
    | some known =>
        dsimp only
        split_ifs
        · apply (resolvedPreservesCachedInput_revealCoordinateOutput tracked coordinate).bind
          intro output
          apply (resolvedPreservesCachedInput_lift tracked _).bind
          intro _
          exact (resolvedPreservesCachedInput_modify tracked _ (fun cache answer hcached => by
            have hkey : SplitHashKey.ordinary tracked ≠ .ordinary input := by simpa using Ne.symm heq
            simpa only [Function.update_of_ne hkey] using hcached)).bind
              fun _ => ResolvedPreservesCachedInput.pure tracked _
        · exact resolvedPreservesCachedInput_splitHashQuery tracked _

theorem resolvedPreservesCachedInput_executeCandidate (input : HashInput) (candidate : Option Probe) :
    ResolvedPreservesCachedInput input (executeCandidate? candidate) := by
  cases candidate with
  | none => exact ResolvedPreservesCachedInput.pure input _
  | some candidate => exact resolvedPreservesCachedInput_lift input _

theorem resolvedPreservesCachedEncoding_afterPlan
    (encodingParameter parameter : PublicParameter) (position : EncodingPosition) (message : Digest) (tracked : HashInput)
    (htracked : tracked ∈ encodingRetryInputs encodingParameter position message) (input : HashInput) (plan : PlannedHashQuery) :
    ResolvedPreservesCachedInput tracked (probingHashQueryAfterPlan parameter input plan) := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  apply (resolvedPreservesCachedInput_executeCandidate tracked plan.candidate?).bind
  intro _
  cases plan.action with
  | ordinary => exact resolvedPreservesCachedInput_splitHashQuery tracked _
  | resolve coordinate => exact resolvedPreservesCachedEncoding_resolveKnownInput encodingParameter parameter position message tracked htracked coordinate input

theorem encodingCacheExtends_of_mem_probingHashQuery
    (parameter : PublicParameter) (input : HashInput)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache))) :
    EncodingCacheExtends (ordinaryQueryCache cache) (ordinaryQueryCache result.value.2) := by
  rw [runResolved_probingHashQuery_eq_afterPlan] at hresult
  intro encodingParameter position message tracked htracked output hcached
  exact resolvedPreservesCachedEncoding_afterPlan encodingParameter parameter position message tracked htracked input
    (purePlanProbingHashQuery parameter input context.state) context fuel table cache result hresult output hcached

end SphincsSecurity.Concrete.OtsProbeSimulation
