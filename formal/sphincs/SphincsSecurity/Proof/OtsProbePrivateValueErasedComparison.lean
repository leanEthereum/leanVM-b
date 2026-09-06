import SphincsSecurity.Proof.OtsProbePrivateValueErasedPrefix

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem evalDist_runResolvedLiveValue_bind
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runResolvedLiveValue table context fuel (left >>= next)) =
      evalDist (runResolvedFromTable context fuel table left >>= fun result =>
        match result with
        | none => pure none
        | some result => runResolvedLiveValue result.table result.context result.remaining (next result.value)) := by
  unfold runResolvedLiveValue
  rw [runResolvedFromTable_bind, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have htable := (resolvedCore_of_mem_runResolvedFromTable left context fuel table result hconsistent hstarts hresult).1
      dsimp only
      rw [htable]

theorem evalDist_runResolvedLiveValue_eq_none_of_not_completable
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (runResolvedLiveValue table context fuel computation) =
      evalDist (pure none : ProbComp (Option (Nat × α))) := by
  unfold runResolvedLiveValue
  calc
    _ = evalDist (runResolvedFromTable context fuel table computation >>= fun _ => pure none) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hfinal := not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result
            hconsistent hstarts hresult hdoomed
          simp only [if_neg hfinal]
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (runResolvedFromTable context fuel table computation) (by simp [runResolvedFromTable]) (pure none)

theorem probEvent_runResolvedLiveValue_add_private_pending_le
    (target : Position) (output : HashOutput) (digest : Digest)
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (event : Option (Nat × α) → Prop) (hnone : ¬event none)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hknown : context.positionValue target = some output)
    (hpending : context.state.pendingAt (.position target) = ∅) :
    Pr[event | runResolvedLiveValue table
      { context with state := context.state.addPending (.position target) digest } fuel computation] ≤
      Pr[event | runResolvedLiveValue table context fuel computation] := by
  let added : DeferredContext := { context with state := context.state.addPending (.position target) digest }
  have hc : added.ValuesConsistent := hconsistent.addPending _ _
  have hs : StartTableAgrees added.state table := hstarts
  change Pr[event | runResolvedLiveValue table added fuel computation] ≤ _
  by_cases hcomplete : DeferredCompletable table added
  · have hv := valid_of_resolvedCore_completable table added hc hs hcomplete
    have hk : added.positionValue target = some output := hknown
    have hdist := evalDist_runResolvedLiveValue_clearPending_known target output table added fuel computation hv hcomplete hk
    have hclear : added.state.clearPending (.position target) = context.state := by
      calc
        _ = context.state.clearPending (.position target) := by
          simp only [added, LazyRevealProbe.State.addPending, LazyRevealProbe.State.clearPending,
            LazyRevealProbe.State.pendingAway, Finset.filter_insert, ne_eq, not_true_eq_false, if_false]
        _ = _ := clearPending_eq_self_of_pendingAt_empty context.state (.position target) hpending
    have hcontext : ({ added with state := added.state.clearPending (.position target) } : DeferredContext) = context := by
      rw [hclear]
    rw [hcontext] at hdist
    exact le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) hdist)
  · have hdist := evalDist_runResolvedLiveValue_eq_none_of_not_completable table added fuel computation hc hs hcomplete
    rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist]
    simp [hnone]

theorem probEvent_runResolvedLiveValue_le_privateErasedPrefixValue
    (target : Position) (output : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (event : Option (Nat × α) → Prop) (hnone : ¬event none)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hprivate : PrivateTargetState target output ∅ context)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0) :
    Pr[event | runResolvedLiveValue table context fuel computation] ≤
      Pr[event | privateErasedPrefixValue target context fuel table computation] := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value =>
      by_cases hcomplete : DeferredCompletable table context <;>
        simp [runResolvedLiveValue, runResolvedFromTable, privateErasedPrefixValue, runPrivateErasedPrefix, hcomplete, hnone]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe
      have hinput : ¬IsPrivatePositionDisclosure target input := by simpa using hsafe.1
      have hnext (reply) : (next reply).IsQueryBoundP (IsPrivatePositionDisclosure target) 0 := by
        simpa using hsafe.2 reply
      by_cases hprobe : IsPrivatePositionProbe target input
      · cases input <;> simp only [IsPrivatePositionProbe] at hprobe
        case probe coordinate digest =>
          subst coordinate
          cases fuel with
          | zero =>
              simp [runResolvedLiveValue, runResolvedFromTable_probe_query_bind, privateErasedPrefixValue,
                runPrivateErasedPrefix_probe_query_bind, hnone]
          | succ fuel =>
              simp only [runResolvedLiveValue, runResolvedFromTable_probe_query_bind, if_neg hprivate.2.2.1,
                privateErasedPrefixValue, runPrivateErasedPrefix_probe_query_bind, true_or, if_true]
              exact (probEvent_runResolvedLiveValue_add_private_pending_le target output digest table context fuel
                (next ()) event hnone hconsistent hstarts
                (by simp [DeferredContext.positionValue, hprivate.1, hprivate.2.1]) hprivate.2.2.2).trans
                (ih () context fuel table hconsistent hstarts hprivate (hnext ()))
      · have hright : privateErasedPrefixValue target context fuel table
            ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) =
            (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)) >>= fun result =>
              match result with
              | none => pure none
              | some result => privateErasedPrefixValue target result.context result.remaining result.table (next result.value)) := by
          unfold privateErasedPrefixValue
          rw [runPrivateErasedPrefix_query_bind_of_not_target_probe target input next context fuel table hprobe, map_bind]
          apply bind_congr
          intro result
          cases result <;> simp only [map_pure, Option.map_none]
        rw [hright, probEvent_congr' (fun _ _ => Iff.rfl)
          (evalDist_runResolvedLiveValue_bind table context fuel (liftM (OracleSpec.query input)) next hconsistent hstarts),
          probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hresult : result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)))
        · cases result with
          | none => rfl
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result
                hconsistent hstarts hresult
              have hnoaccess : (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _).IsQueryBoundP
                  (IsPrivatePositionAccess target) 0 := by
                cases input <;> simp_all [IsPrivatePositionAccess, IsPrivatePositionDisclosure, IsPrivatePositionProbe]
              have hprivate' := hprivate.of_mem_runResolved_no_access (liftM (OracleSpec.query input)) context fuel table result
                hnoaccess hresult
              exact mul_le_mul' le_rfl
                (ih result.value result.context result.remaining result.table hcore.2.1 (hcore.1 ▸ hcore.2.2) hprivate' (hnext result.value))
        · simp [probOutput_eq_zero_of_not_mem_support hresult]

end SphincsSecurity.Concrete.OtsProbeSimulation
