import SphincsSecurity.Proof.OtsProbePrivateValueProbeRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def privateProbeHistoryStep (target : Position) (pending : Finset Digest) :
    LazyRevealProbe.Query Coordinate → Finset Digest
  | .probe coordinate digest => if coordinate = .position target then insert digest pending else pending
  | _ => pending

noncomputable def trackPrivateProbeHistory
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Finset Digest → OracleComp (LazyRevealProbe.World Coordinate) (Finset Digest × α) :=
  OracleComp.construct (fun value pending => pure (pending, value))
    (fun input _ recursivelyTrack pending =>
      (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
        fun reply => recursivelyTrack reply (privateProbeHistoryStep target pending input)) computation

theorem trackPrivateProbeHistory_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (pending : Finset Digest) :
    trackPrivateProbeHistory target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) pending =
      (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
        fun reply => trackPrivateProbeHistory target (next reply) (privateProbeHistoryStep target pending input) := rfl

theorem trackPrivateProbeHistory_erase
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (pending : Finset Digest) :
    Prod.snd <$> trackPrivateProbeHistory target computation pending = computation := by
  induction computation using OracleComp.inductionOn generalizing pending with
  | pure value => rfl
  | query_bind input next ih =>
      rw [trackPrivateProbeHistory_query_bind, map_bind]
      exact bind_congr fun reply => ih reply _

theorem trackPrivateProbeHistory_query_bound
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (pending : Finset Digest)
    (predicate : LazyRevealProbe.Query Coordinate → Prop) (bound : Nat)
    (hbound : computation.IsQueryBoundP predicate bound) :
    (trackPrivateProbeHistory target computation pending).IsQueryBoundP predicate bound := by
  induction computation using OracleComp.inductionOn generalizing pending bound with
  | pure value => simp [trackPrivateProbeHistory]
  | query_bind input next ih =>
      rw [trackPrivateProbeHistory_query_bind, OracleComp.isQueryBoundP_query_bind_iff]
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      exact ⟨hbound.1, fun reply => ih reply _ _ (hbound.2 reply)⟩

def recordPrivateHistory (target : Position) (result : ResolvedRunResult α) : ResolvedRunResult (Finset Digest × α) :=
  ⟨result.context, result.remaining, (result.context.state.pendingAt (.position target), result.value), result.table⟩

theorem evalDist_runResolved_trackPrivateProbeHistory
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest)
    (h : PrivateTargetState target output pending context)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0) :
    evalDist (runResolvedFromTable context fuel table (trackPrivateProbeHistory target computation pending)) =
      evalDist (Option.map (recordPrivateHistory target) <$> runResolvedFromTable context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel pending with
  | pure value =>
      change evalDist (pure (some ⟨context, fuel, (pending, value), table⟩)) =
        evalDist (pure (some (recordPrivateHistory target ⟨context, fuel, value, table⟩)))
      simp [recordPrivateHistory, h.2.2.2]
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe
      have hquery : ¬IsPrivatePositionDisclosure target query := by simpa using hsafe.1
      have hnext : ∀ reply, (next reply).IsQueryBoundP (IsPrivatePositionDisclosure target) 0 := by
        intro reply
        simpa using hsafe.2 reply
      rw [trackPrivateProbeHistory_query_bind]
      cases query with
      | uniform n =>
          simp only [runResolvedFromTable_uniform_query_bind, map_bind, privateProbeHistoryStep]
          apply evalDist_bind_congr
          intro reply _
          exact ih reply context fuel pending h (hnext reply)
      | hashOutput =>
          simp only [runResolvedFromTable_hashOutput_query_bind, map_bind, privateProbeHistoryStep]
          apply evalDist_bind_congr
          intro reply _
          exact ih reply context fuel pending h (hnext reply)
      | ensure coordinate =>
          simp only [runResolvedFromTable_ensure_query_bind, privateProbeHistoryStep]
          exact ih () { context with state := context.state.ensure coordinate } fuel pending h (hnext ())
      | peek coordinate =>
          simp only [runResolvedFromTable_peek_query_bind, privateProbeHistoryStep]
          exact ih _ context fuel pending h (hnext _)
      | publish coordinate =>
          simp only [runResolvedFromTable_publish_query_bind, privateProbeHistoryStep]
          exact ih () _ fuel pending (h.publish_other coordinate hquery) (hnext ())
      | probe coordinate digest =>
          simp only [runResolvedFromTable_probe_query_bind, privateProbeHistoryStep]
          cases fuel with
          | zero => simp
          | succ remaining =>
              dsimp only
              by_cases htarget : coordinate = .position target
              · subst coordinate
                simp only [if_neg h.2.2.1, if_true]
                exact ih () _ remaining (insert digest pending) (h.probe_target digest) (hnext ())
              · rw [if_neg htarget]
                split_ifs
                · exact ih () context remaining pending h (hnext ())
                · exact ih () _ remaining pending (h.probe_other coordinate digest htarget) (hnext ())
      | reveal coordinate =>
          simp only [runResolvedFromTable_reveal_query_bind, privateProbeHistoryStep]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [pure_bind]
              cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
              | none => simp
              | some middle =>
                  have hvalues := resolveDeferredChainStart_deferred_values_eq table ⟨lay, tree, leafIdx, chainIdx⟩ context middle hresolved
                  exact ih middle.output _ fuel pending
                    (h.materialize_other _ middle.output middle.values (by simp) (hvalues ▸ h.2.1)) (hnext middle.output)
          | position position =>
              dsimp only
              simp only [map_bind]
              apply evalDist_bind_congr
              intro option hresolve
              cases option with
              | none => simp
              | some middle =>
                  have hvalue := privateValue_preserved_by_resolveDeferredReveal target position output table context middle h.1 h.2.1 hresolve
                  exact ih middle.output _ fuel pending (h.materialize_other _ middle.output middle.values hquery hvalue) (hnext middle.output)


def privateHistoryValue (target : Position) (result : Option (ResolvedRunResult α)) : Option (Nat × Finset Digest × α) :=
  result.map (fun record => (record.remaining, record.context.state.pendingAt (.position target), record.value))

theorem evalDist_runResolvedLiveValue_trackPrivateProbeHistory
    (target : Position) (output : HashOutput) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (pending : Finset Digest)
    (h : PrivateTargetState target output pending context)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0) :
    evalDist (runResolvedLiveValue table context fuel (trackPrivateProbeHistory target computation pending)) =
      evalDist ((fun result => privateHistoryValue target (retainCompletableResult result)) <$>
        runResolvedFromTable context fuel table computation) := by
  rw [evalDist_runResolvedLiveValue_eq_retained_value table context fuel _ hconsistent hstarts]
  have hdist := evalDist_runResolved_trackPrivateProbeHistory target output computation context fuel table pending h hsafe
  calc
    _ = evalDist ((fun result => (retainCompletableResult result).map (fun result => (result.remaining, result.value))) <$>
        (Option.map (recordPrivateHistory target) <$> runResolvedFromTable context fuel table computation)) :=
      evalDist_map_eq_of_evalDist_eq hdist _
    _ = _ := by
      rw [Functor.map_map]
      congr 2
      funext result
      cases result with
      | none => rfl
      | some result =>
          by_cases hcomplete : DeferredCompletable result.table result.context <;>
            simp [retainCompletableResult, recordPrivateHistory, privateHistoryValue, hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation
