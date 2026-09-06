import SphincsSecurity.Proof.OtsProbeProbeFreePreload
import SphincsSecurity.Proof.OtsProbePrivateValueProbeCounting
import SphincsSecurity.Proof.OtsProbeCanonicalFuel

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def commonPrivateCutCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) : ENNReal :=
  Pr[PrivateProbeCutReached target | runResolvedFromTable context 0 table
    (eraseProbeQueries (privatePositionProbeCutAt target computation ordinal))]

theorem privateErasedCandidateCharge_le_common
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hvalid : context.Valid) (hstarts : StartTableAgrees context.state table) (hcovered : PendingCovered [] context)
    (hensured : .position target ∈ context.state.ensured)
    (hstate : context.state.values (.position target) = none) (hvalue : context.values target = none) :
    privateErasedCandidateCharge target (privateRawCutCandidate target) (privatePositionProbeCutAt target computation ordinal)
      context fuel table ≤ commonPrivateCutCharge target computation context table ordinal := by
  unfold privateErasedCandidateCharge privateRawCutCandidate
  apply (probEvent_privateErasedCandidate_le_probeFree target (fun cut => privatePositionAccessCandidate target (some cut))
    (privatePositionProbeCutAt target computation ordinal) context fuel table 0).trans_eq
  have hd := evalDist_rawResolvedValue_probeFree_preload target 0
    (eraseProbeQueries (privatePositionProbeCutAt target computation ordinal)) context 0 table hvalid hstarts hcovered
    hensured hstate hvalue (eraseProbeQueries_probeFree _)
    (eraseProbeQueries_no_access target _ (privatePositionProbeCutAt_no_disclosure target computation ordinal))
  have hp := probEvent_congr' (fun _ _ => Iff.rfl) hd (p := fun result =>
    privatePositionAccessCandidate target (result.map Prod.snd) ≠ none)
  simp only [probEvent_map, Function.comp_def] at hp
  have heq : (fun result : Option (ResolvedRunResult (PrivateValueCut α)) =>
      privatePositionAccessCandidate target ((rawResolvedResultValue result).map Prod.snd) ≠ none) = PrivateProbeCutReached target := by
    funext result
    cases result <;> rfl
  rw [heq] at hp
  apply Eq.trans _ hp
  apply probEvent_congr' _ rfl
  intro result _
  cases result <;> rfl

theorem eraseProbeQueries_query_bind
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α) :
    eraseProbeQueries ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) =
      eraseProbeQueries (liftM (OracleSpec.query input)) >>= fun output => eraseProbeQueries (next output) := by
  cases input <;> simp [eraseProbeQueries]

noncomputable def erasedStructuralQueryCharge
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : DeferredContext → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ => 0) (fun input _ next context table =>
    structuralProbeQueryCharge input +
      ∑' result, Pr[= result | runResolvedFromTable context 0 table (eraseProbeQueries (liftM (OracleSpec.query input)))] *
        match result with
        | none => 0
        | some result => next result.value result.context result.table) computation

theorem erasedStructuralQueryCharge_query_bind
    (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) :
    erasedStructuralQueryCharge ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context table =
      structuralProbeQueryCharge input +
        ∑' result, Pr[= result | runResolvedFromTable context 0 table (eraseProbeQueries (liftM (OracleSpec.query input)))] *
          match result with
          | none => 0
          | some result => erasedStructuralQueryCharge (next result.value) result.context result.table := rfl

theorem commonPrivateCutCharge_query_bind_of_no_access
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hdisclose : ¬IsPrivatePositionDisclosure target input) (hprobe : ¬IsPrivatePositionProbe target input) :
    commonPrivateCutCharge target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context table ordinal =
      ∑' result, Pr[= result | runResolvedFromTable context 0 table (eraseProbeQueries (liftM (OracleSpec.query input)))] *
        match result with
        | none => 0
        | some result => commonPrivateCutCharge target (next result.value) result.context result.table ordinal := by
  unfold commonPrivateCutCharge
  rw [privatePositionProbeCutAt_query_bind, if_neg hdisclose, if_neg hprobe, eraseProbeQueries_query_bind,
    runResolvedFromTable_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (runResolvedFromTable context 0 table (eraseProbeQueries (liftM (OracleSpec.query input))))
  · cases result with
    | none => simp [PrivateProbeCutReached, privatePositionAccessCandidate]
    | some result =>
        have hz : result.remaining = 0 := Nat.eq_zero_of_le_zero
          (fuel_bounds_of_mem_runResolvedFromTable _ context 0 0 table result (eraseProbeQueries_probeFree _) hresult).1
        simp only [hz]
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem commonPrivateCutCharge_disclosure
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (hdisclose : IsPrivatePositionDisclosure target input) :
    commonPrivateCutCharge target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context table ordinal = 0 := by
  unfold commonPrivateCutCharge
  rw [privatePositionProbeCutAt_query_bind, if_pos hdisclose]
  cases input <;> simp_all [IsPrivatePositionDisclosure, eraseProbeQueries, runResolvedFromTable,
    PrivateProbeCutReached, privatePositionAccessCandidate]

theorem commonPrivateCutCharge_probe_target_zero
    (target : Position) (digest : Digest) (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) :
    commonPrivateCutCharge target ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe (.position target) digest)) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context table 0 = 1 := by
  unfold commonPrivateCutCharge
  rw [privatePositionProbeCutAt_query_bind target (.probe (.position target) digest) next 0]
  simp [IsPrivatePositionDisclosure, IsPrivatePositionProbe,
    eraseProbeQueries, runResolvedFromTable, PrivateProbeCutReached, privatePositionAccessCandidate]

theorem commonPrivateCutCharge_probe_target_succ
    (target : Position) (digest : Digest) (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (ordinal : Nat) :
    commonPrivateCutCharge target ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe (.position target) digest)) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context table (ordinal + 1) = commonPrivateCutCharge target (next ()) context table ordinal := by
  unfold commonPrivateCutCharge
  rw [privatePositionProbeCutAt_query_bind target (.probe (.position target) digest) next (ordinal + 1)]
  simp only [IsPrivatePositionDisclosure, IsPrivatePositionProbe, if_false, if_true, eraseProbeQueries, OracleComp.construct_query_bind]

theorem sum_commonPrivateCutCharge_query_bind_le
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (q : Nat) :
    (∑ ordinal ∈ Finset.range q, commonPrivateCutCharge target
      ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) context table ordinal) ≤
      privatePositionProbeQueryCharge target input +
        ∑' result, Pr[= result | runResolvedFromTable context 0 table (eraseProbeQueries (liftM (OracleSpec.query input)))] *
          match result with
          | none => 0
          | some result => ∑ ordinal ∈ Finset.range q, commonPrivateCutCharge target (next result.value) result.context result.table ordinal := by
  by_cases hdisclose : IsPrivatePositionDisclosure target input
  · simp only [commonPrivateCutCharge_disclosure target input next context table _ hdisclose, Finset.sum_const_zero]
    exact bot_le
  · by_cases hprobe : IsPrivatePositionProbe target input
    · cases input <;> simp only [IsPrivatePositionProbe] at hprobe
      case probe coordinate digest =>
        subst coordinate
        have hstep : runResolvedFromTable context 0 table
            (eraseProbeQueries (liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.probe (.position target) digest)))) =
            pure (some (⟨context, 0, (), table⟩ : ResolvedRunResult Unit)) := rfl
        rw [hstep, tsum_probOutput_pure_mul]
        simp only [privatePositionProbeQueryCharge, IsPrivatePositionProbe, if_true]
        cases q with
        | zero => simp
        | succ q =>
            rw [Finset.sum_range_succ']
            rw [commonPrivateCutCharge_probe_target_zero target digest next context table]
            simp_rw [commonPrivateCutCharge_probe_target_succ target digest next context table]
            rw [add_comm]
            apply add_le_add le_rfl
            exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ q))
    · simp only [privatePositionProbeQueryCharge, if_neg hprobe, zero_add]
      apply le_of_eq
      simp_rw [commonPrivateCutCharge_query_bind_of_no_access target input next context table _ hdisclose hprobe]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply tsum_congr
      intro result
      cases result <;> simp [Finset.mul_sum]

theorem sum_commonPrivateCutCharge_le_erasedStructuralCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (q : Nat) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q, commonPrivateCutCharge target computation context table ordinal) ≤
      erasedStructuralQueryCharge computation context table := by
  induction computation using OracleComp.inductionOn generalizing context table with
  | pure value =>
      simp [commonPrivateCutCharge, privatePositionProbeCutAt, eraseProbeQueries, runResolvedFromTable,
        PrivateProbeCutReached, privatePositionAccessCandidate, erasedStructuralQueryCharge]
  | query_bind input next ih =>
      rw [erasedStructuralQueryCharge_query_bind]
      apply (Finset.sum_le_sum (fun target _ => sum_commonPrivateCutCharge_query_bind_le target input next context table q)).trans
      rw [Finset.sum_add_distrib, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply add_le_add (sum_privatePositionProbeQueryCharge_le_structural targets input)
      apply ENNReal.tsum_le_tsum
      intro result
      cases result with
      | none => simp
      | some result =>
          simp only [← Finset.mul_sum]
          exact mul_le_mul' le_rfl (ih result.value result.context result.table)

theorem erasedStructuralQueryCharge_le_probeBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    erasedStructuralQueryCharge computation context table ≤ q := by
  induction computation using OracleComp.inductionOn generalizing context table q with
  | pure value => exact bot_le
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [erasedStructuralQueryCharge_query_bind]
      let cost : Nat := if LazyRevealProbe.IsProbe input then 1 else 0
      have hcost : structuralProbeQueryCharge input ≤ cost := by
        cases input with
        | probe coordinate digest => cases coordinate <;> simp [structuralProbeQueryCharge, cost, LazyRevealProbe.IsProbe]
        | _ => simp [structuralProbeQueryCharge, cost, LazyRevealProbe.IsProbe]
      have hle : cost ≤ q := by
        by_cases hp : LazyRevealProbe.IsProbe input
        · have hpos := hbound.1.resolve_left (not_not.mpr hp)
          simp only [cost, if_pos hp]
          omega
        · simp [cost, hp]
      have htail : (∑' result, Pr[= result | runResolvedFromTable context 0 table (eraseProbeQueries (liftM (OracleSpec.query input)))] *
          match result with
          | none => 0
          | some result => erasedStructuralQueryCharge (next result.value) result.context result.table) ≤ ((q - cost : Nat) : ENNReal) := by
        calc
          _ ≤ ∑' result, Pr[= result | runResolvedFromTable context 0 table (eraseProbeQueries (liftM (OracleSpec.query input)))] *
              ((q - cost : Nat) : ENNReal) := by
            apply ENNReal.tsum_le_tsum
            intro result
            apply mul_le_mul' le_rfl
            cases result with
            | none => exact bot_le
            | some result =>
                apply ih result.value result.context result.table (q - cost)
                by_cases hp : LazyRevealProbe.IsProbe input <;> simpa [cost, hp] using hbound.2 result.value
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one
      exact (add_le_add hcost htail).trans_eq (by rw [← Nat.cast_add, Nat.add_sub_of_le hle])

end SphincsSecurity.Concrete.OtsProbeSimulation
