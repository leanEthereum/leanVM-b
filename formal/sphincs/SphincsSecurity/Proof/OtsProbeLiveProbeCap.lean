import SphincsSecurity.Proof.OtsProbeCommonPrivateGame
import SphincsSecurity.Proof.OtsProbeNativeLiveBudget

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def privateCutValue : PrivateValueCut α → Option α
  | .done value => some value
  | .query _ _ => none

noncomputable def capProbeQueries (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat) :
    OracleComp (LazyRevealProbe.World Coordinate) (Option α) := privateCutValue <$> nativeProbeCutAt computation q

theorem capProbeQueries_query_bind
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat) :
    capProbeQueries ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) q =
      (if LazyRevealProbe.IsProbe input then
        match q with
        | 0 => pure none
        | q + 1 => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun reply => capProbeQueries (next reply) q
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun reply => capProbeQueries (next reply) q) := by
  unfold capProbeQueries
  rw [nativeProbeCutAt_query_bind]
  split_ifs
  · cases q <;> simp [map_bind, privateCutValue]
  · rw [map_bind]

theorem capProbeQueries_probeBound (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat) :
    (capProbeQueries computation q).IsQueryBoundP LazyRevealProbe.IsProbe q := by
  simpa only [capProbeQueries, isQueryBoundP_map_iff] using nativeProbeCutAt_probeBound computation q

theorem evalDist_runPrivateResolvedView_eq_none_of_not_completable
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (runPrivateResolvedView target table context fuel computation) =
      evalDist (pure none : ProbComp (Option (DeferredContext × Nat × α))) := by
  unfold runPrivateResolvedView
  calc
    _ = evalDist (runResolvedFromTable context fuel table computation >>= fun _ => pure none) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult
          exact evalDist_privateResolutionResult_eq_none_of_not_completable target table result.context result.remaining result.value
            hcore.2.1
            (not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result hconsistent hstarts hresult hdoomed)
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (runResolvedFromTable context fuel table computation) (by simp [runResolvedFromTable]) _

theorem evalDist_runPrivateResolvedView_bind
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (runPrivateResolvedView target table context fuel (left >>= next)) =
      evalDist (runResolvedFromTable context fuel table left >>= fun result =>
        match result with
        | none => pure none
        | some result => runPrivateResolvedView target result.table result.context result.remaining (next result.value)) := by
  unfold runPrivateResolvedView
  rw [runResolvedFromTable_bind, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have htable := (resolvedCore_of_mem_runResolvedFromTable left context fuel table result hconsistent hstarts hresult).1
      dsimp only
      rw [htable]

theorem privateResolutionResult_map
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (value : α) (f : α → β) :
    privateResolutionResult target table context fuel (f value) =
      (Option.map (fun result => (result.1, result.2.1, f result.2.2))) <$>
        privateResolutionResult target table context fuel value := by
  unfold privateResolutionResult
  rw [map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => simp
  | some result =>
      dsimp only
      split_ifs <;> simp

theorem runPrivateResolvedView_map
    (target : Position) (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (f : α → β) :
    runPrivateResolvedView target table context fuel (f <$> computation) =
      (Option.map (fun result => (result.1, result.2.1, f result.2.2))) <$>
        runPrivateResolvedView target table context fuel computation := by
  unfold runPrivateResolvedView
  rw [map_eq_bind_pure_comp, runResolvedFromTable_bind, bind_assoc, map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => simp
  | some result =>
      simp only [Function.comp_apply, runResolvedFromTable, construct_pure, pure_bind]
      exact privateResolutionResult_map target table result.context result.remaining result.value f

noncomputable def privateProbeCandidateCut (target : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    OracleComp (LazyRevealProbe.World Coordinate) (Option Digest) :=
  privateRawCutCandidate target 0 <$> privatePositionProbeCutAt target computation ordinal

theorem privateProbeCandidateCut_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α) (ordinal : Nat) :
    privateProbeCandidateCut target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) ordinal =
      (if IsPrivatePositionDisclosure target input then pure none
      else if IsPrivatePositionProbe target input then
        match ordinal with
        | 0 => pure (privatePositionAccessCandidate target (some (.query input next)))
        | ordinal + 1 => (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun reply => privateProbeCandidateCut target (next reply) ordinal
      else (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun reply => privateProbeCandidateCut target (next reply) ordinal) := by
  unfold privateProbeCandidateCut
  rw [privatePositionProbeCutAt_query_bind]
  split_ifs with hdisclose hprobe
  · cases input <;> simp_all [IsPrivatePositionDisclosure, privateRawCutCandidate, privatePositionAccessCandidate]
  · cases ordinal <;> simp [map_bind, privateRawCutCandidate]
  · rw [map_bind]

theorem capProbeQueries_query_bind_of_positive
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (hpositive : LazyRevealProbe.IsProbe input → 0 < q) :
    capProbeQueries ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) q =
      (liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= fun reply =>
        capProbeQueries (next reply) (if LazyRevealProbe.IsProbe input then q - 1 else q) := by
  rw [capProbeQueries_query_bind]
  split_ifs with hprobe
  · cases q with
    | zero => exact (Nat.lt_irrefl 0 (hpositive hprobe)).elim
    | succ q => rfl
  · rfl

theorem privatePositionAccessCandidate_query_continuation
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (left : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (right : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) β) :
    privatePositionAccessCandidate target (some (.query input left)) =
      privatePositionAccessCandidate target (some (.query input right)) := by
  cases input <;> rfl

theorem evalDist_privateProbeCandidateCut_cap
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (q ordinal : Nat)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbound : LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q context fuel table) :
    evalDist (runPrivateResolvedView target table context fuel (privateProbeCandidateCut target computation ordinal)) =
      evalDist (runPrivateResolvedView target table context fuel
        (privateProbeCandidateCut target (capProbeQueries computation q) ordinal)) := by
  induction computation using OracleComp.inductionOn generalizing context fuel table q ordinal with
  | pure value => rfl
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · have hbound := (liveResolvedQueryBound_query_bind _ _ _ _ _ _ _).mp hbound hcomplete
        rw [capProbeQueries_query_bind_of_positive input next q hbound.1]
        simp only [privateProbeCandidateCut_query_bind]
        by_cases hdisclose : IsPrivatePositionDisclosure target input
        · simp only [if_pos hdisclose]
        · simp only [if_neg hdisclose]
          by_cases hprobe : IsPrivatePositionProbe target input
          · simp only [if_pos hprobe]
            cases ordinal with
            | zero => rw [privatePositionAccessCandidate_query_continuation target input next]
            | succ ordinal =>
                rw [evalDist_runPrivateResolvedView_bind target table context fuel _ _ hconsistent hstarts,
                  evalDist_runPrivateResolvedView_bind target table context fuel _ _ hconsistent hstarts]
                apply evalDist_bind_congr
                intro result hresult
                cases result with
                | none => rfl
                | some result =>
                    have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
                    exact ih result.value result.context result.remaining result.table _ ordinal hcore.2.1
                      (by rw [hcore.1]; exact hcore.2.2) (by by_cases hp : LazyRevealProbe.IsProbe input <;> simpa only [hp, if_true, if_false] using hbound.2 result hresult)
          · simp only [if_neg hprobe]
            rw [evalDist_runPrivateResolvedView_bind target table context fuel _ _ hconsistent hstarts,
              evalDist_runPrivateResolvedView_bind target table context fuel _ _ hconsistent hstarts]
            apply evalDist_bind_congr
            intro result hresult
            cases result with
            | none => rfl
            | some result =>
                have hcore := resolvedCore_of_mem_runResolvedFromTable (liftM (OracleSpec.query input)) context fuel table result hconsistent hstarts hresult
                exact ih result.value result.context result.remaining result.table _ ordinal hcore.2.1
                  (by rw [hcore.1]; exact hcore.2.2) (by by_cases hp : LazyRevealProbe.IsProbe input <;> simpa only [hp, if_true, if_false] using hbound.2 result hresult)
      · rw [evalDist_runPrivateResolvedView_eq_none_of_not_completable target table context fuel _ hconsistent hstarts hcomplete,
          evalDist_runPrivateResolvedView_eq_none_of_not_completable target table context fuel _ hconsistent hstarts hcomplete]

theorem privateResolvedRawCandidate_eq_candidateCut
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) :
    privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal) =
    privateResolvedSelectedCandidate target (fun _ value => value) <$>
      runPrivateResolvedView target table context fuel (privateProbeCandidateCut target computation ordinal) := by
  rw [privateProbeCandidateCut, runPrivateResolvedView_map, Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

theorem evalDist_privateResolvedRawCandidate_cap
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (q ordinal : Nat)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hbound : LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q context fuel table) :
    evalDist (privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)) =
    evalDist (privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
      runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target (capProbeQueries computation q) ordinal)) := by
  rw [privateResolvedRawCandidate_eq_candidateCut, privateResolvedRawCandidate_eq_candidateCut]
  exact evalDist_map_eq_of_evalDist_eq
    (evalDist_privateProbeCandidateCut_cap target computation context fuel table q ordinal hconsistent hstarts hbound) _

end SphincsSecurity.Concrete.OtsProbeSimulation
