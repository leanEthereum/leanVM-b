import SphincsSecurity.Proof.OtsProbePrivateValueRawProbeRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedResolvedQueryCharge
    (charge : LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next context fuel table =>
      charge input + ∑' result,
        Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => next result.value result.context result.remaining result.table) computation

theorem expectedResolvedQueryCharge_query_bind
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge charge ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      context fuel table = charge input + ∑' result,
        Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
          match result with
          | none => 0
          | some result => expectedResolvedQueryCharge charge (next result.value) result.context result.remaining result.table := rfl

noncomputable def privateProbeOrdinalMass
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next ordinal context fuel table =>
      if IsPrivatePositionDisclosure target input then 0
      else if IsPrivatePositionProbe target input ∧ ordinal = 0 then 1
      else ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
        match result with
        | none => 0
        | some result => next result.value (if IsPrivatePositionProbe target input then ordinal - 1 else ordinal)
            result.context result.remaining result.table) computation

theorem privateProbeOrdinalMass_query_bind
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    privateProbeOrdinalMass target ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      ordinal context fuel table =
      (if IsPrivatePositionDisclosure target input then 0
      else if IsPrivatePositionProbe target input ∧ ordinal = 0 then 1
      else ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
        match result with
        | none => 0
        | some result => privateProbeOrdinalMass target (next result.value)
            (if IsPrivatePositionProbe target input then ordinal - 1 else ordinal) result.context result.remaining result.table) := rfl

theorem probEvent_privateProbeCutReached_eq_ordinalMass
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[PrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] =
      privateProbeOrdinalMass target computation ordinal context fuel table := by
  induction computation using OracleComp.inductionOn generalizing ordinal context fuel table with
  | pure value => simp [privatePositionProbeCutAt, runResolvedFromTable, privateProbeOrdinalMass,
      PrivateProbeCutReached, privatePositionAccessCandidate]
  | query_bind input next ih =>
      rw [privatePositionProbeCutAt_query_bind, privateProbeOrdinalMass_query_bind]
      by_cases hdisclose : IsPrivatePositionDisclosure target input
      · rw [if_pos hdisclose, if_pos hdisclose]
        cases input <;> simp [IsPrivatePositionDisclosure] at hdisclose <;>
          simp [runResolvedFromTable, PrivateProbeCutReached, privatePositionAccessCandidate]
      · rw [if_neg hdisclose, if_neg hdisclose]
        have htail (n : Nat) :
            Pr[PrivateProbeCutReached target | runResolvedFromTable context fuel table
              ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>=
                fun reply => privatePositionProbeCutAt target (next reply) n)] =
            ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
              match result with
              | none => 0
              | some result => privateProbeOrdinalMass target (next result.value) n result.context result.remaining result.table := by
          rw [runResolvedFromTable_bind, probEvent_bind_eq_tsum]
          apply tsum_congr
          intro result
          cases result with
          | none => simp [PrivateProbeCutReached, privatePositionAccessCandidate]
          | some result => simp only [ih]
        by_cases hprobe : IsPrivatePositionProbe target input
        · rw [if_pos hprobe]
          cases ordinal with
          | zero =>
              simp only [hprobe, and_self, if_true]
              cases input <;> simp [IsPrivatePositionProbe] at hprobe
              subst_vars
              simp [runResolvedFromTable, PrivateProbeCutReached, privatePositionAccessCandidate]
          | succ ordinal =>
              simp only [hprobe, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, if_true, Nat.add_sub_cancel]
              rw [htail ordinal]
              apply tsum_congr
              intro result
              cases result <;> rfl
        · simp only [hprobe, false_and, if_false]
          rw [htail ordinal]
          apply tsum_congr
          intro result
          cases result <;> rfl

noncomputable def privatePositionProbeQueryCharge (target : Position) (input : LazyRevealProbe.Query Coordinate) : ENNReal :=
  if IsPrivatePositionProbe target input then 1 else 0

theorem sum_privateProbeOrdinalMass_le_expectedCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    (∑ ordinal ∈ Finset.range q, privateProbeOrdinalMass target computation ordinal context fuel table) ≤
      expectedResolvedQueryCharge (privatePositionProbeQueryCharge target) computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value => simp [privateProbeOrdinalMass, expectedResolvedQueryCharge]
  | query_bind input next ih =>
      rw [expectedResolvedQueryCharge_query_bind]
      by_cases hdisclose : IsPrivatePositionDisclosure target input
      · simp [privateProbeOrdinalMass_query_bind, hdisclose]
      · have htail (n : Nat) :
            (∑ ordinal ∈ Finset.range n, ∑' result,
              Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
                match result with
                | none => 0
                | some result => privateProbeOrdinalMass target (next result.value) ordinal result.context result.remaining result.table) ≤
            ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
              match result with
              | none => 0
              | some result => expectedResolvedQueryCharge (privatePositionProbeQueryCharge target)
                  (next result.value) result.context result.remaining result.table := by
          rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          apply ENNReal.tsum_le_tsum
          intro result
          cases result with
          | none => simp
          | some result =>
              simp only [← Finset.mul_sum]
              exact mul_le_mul' le_rfl (ih result.value n result.context result.remaining result.table)
        by_cases hprobe : IsPrivatePositionProbe target input
        · cases q with
          | zero => simp
          | succ q =>
              rw [Finset.sum_range_succ']
              simp only [privateProbeOrdinalMass_query_bind, if_neg hdisclose, hprobe, Nat.add_eq_zero_iff,
                Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel, and_self, if_true,
                privatePositionProbeQueryCharge]
              exact (add_le_add (htail q) (le_refl 1)).trans_eq (add_comm _ _)
        · simp only [privateProbeOrdinalMass_query_bind, if_neg hdisclose, hprobe, false_and, if_false,
            privatePositionProbeQueryCharge, zero_add]
          exact htail q

theorem sum_probEvent_privateProbeCutReached_le_expectedCharge
    (target : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    (∑ ordinal ∈ Finset.range q,
      Pr[PrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)]) ≤
      expectedResolvedQueryCharge (privatePositionProbeQueryCharge target) computation context fuel table := by
  simp_rw [probEvent_privateProbeCutReached_eq_ordinalMass]
  exact sum_privateProbeOrdinalMass_le_expectedCharge target computation q context fuel table


theorem expectedResolvedQueryCharge_mono
    (left right : LazyRevealProbe.Query Coordinate → ENNReal) (hle : ∀ input, left input ≤ right input)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge left computation context fuel table ≤ expectedResolvedQueryCharge right computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedResolvedQueryCharge_query_bind, expectedResolvedQueryCharge_query_bind]
      apply add_le_add (hle input)
      apply ENNReal.tsum_le_tsum
      intro result
      cases result with
      | none => rfl
      | some result => exact mul_le_mul' le_rfl (ih result.value result.context result.remaining result.table)

theorem expectedResolvedQueryCharge_finset_sum
    (indices : Finset ι) (charge : ι → LazyRevealProbe.Query Coordinate → ENNReal)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    expectedResolvedQueryCharge (fun input => ∑ index ∈ indices, charge index input) computation context fuel table =
      ∑ index ∈ indices, expectedResolvedQueryCharge (charge index) computation context fuel table := by
  induction computation using OracleComp.inductionOn generalizing context fuel table with
  | pure value => simp [expectedResolvedQueryCharge]
  | query_bind input next ih =>
      simp only [expectedResolvedQueryCharge_query_bind, Finset.sum_add_distrib]
      congr 1
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply tsum_congr
      intro result
      cases result with
      | none => simp
      | some result =>
          simp only [← Finset.mul_sum]
          rw [ih]

noncomputable def structuralProbeQueryCharge : LazyRevealProbe.Query Coordinate → ENNReal
  | .probe (.position _) _ => 1
  | _ => 0

theorem sum_privatePositionProbeQueryCharge_le_structural
    (targets : Finset Position) (input : LazyRevealProbe.Query Coordinate) :
    (∑ target ∈ targets, privatePositionProbeQueryCharge target input) ≤ structuralProbeQueryCharge input := by
  cases input with
  | uniform n => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | hashOutput => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | ensure coordinate => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | peek coordinate => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | publish coordinate => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | reveal coordinate => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
  | probe coordinate digest =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx => simp [privatePositionProbeQueryCharge, IsPrivatePositionProbe, structuralProbeQueryCharge]
      | position position =>
          simp only [privatePositionProbeQueryCharge, IsPrivatePositionProbe, Coordinate.position.injEq, structuralProbeQueryCharge]
          rw [Finset.sum_ite_eq]
          split_ifs <;> simp

theorem sum_targets_privateProbeCutReached_le_expectedStructuralCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)]) ≤
      expectedResolvedQueryCharge structuralProbeQueryCharge computation context fuel table := by
  calc
    _ ≤ ∑ target ∈ targets, expectedResolvedQueryCharge (privatePositionProbeQueryCharge target) computation context fuel table :=
      Finset.sum_le_sum (fun target _ => sum_probEvent_privateProbeCutReached_le_expectedCharge target computation q context fuel table)
    _ = expectedResolvedQueryCharge (fun input => ∑ target ∈ targets, privatePositionProbeQueryCharge target input) computation context fuel table :=
      (expectedResolvedQueryCharge_finset_sum targets privatePositionProbeQueryCharge computation context fuel table).symm
    _ ≤ _ := expectedResolvedQueryCharge_mono _ _ (sum_privatePositionProbeQueryCharge_le_structural targets) computation context fuel table


theorem expectedResolvedQueryCharge_le_queryBound
    (charge : LazyRevealProbe.Query Coordinate → ENNReal) (predicate : LazyRevealProbe.Query Coordinate → Prop) [DecidablePred predicate]
    (hcharge : ∀ input, charge input ≤ if predicate input then 1 else 0)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (bound : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP predicate bound) :
    expectedResolvedQueryCharge charge computation context fuel table ≤ bound := by
  induction computation using OracleComp.inductionOn generalizing bound context fuel table with
  | pure value => simp [expectedResolvedQueryCharge]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [expectedResolvedQueryCharge_query_bind]
      let remaining := if predicate input then bound - 1 else bound
      have htail :
          (∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] *
            match result with
            | none => 0
            | some result => expectedResolvedQueryCharge charge (next result.value) result.context result.remaining result.table) ≤ remaining := by
        calc
          _ ≤ ∑' result, Pr[= result | runResolvedFromTable context fuel table (liftM (OracleSpec.query input))] * (remaining : ENNReal) := by
            apply ENNReal.tsum_le_tsum
            intro result
            apply mul_le_mul' le_rfl
            cases result with
            | none => exact bot_le
            | some result => exact ih result.value remaining result.context result.remaining result.table (hbound.2 result.value)
          _ = _ := by
            rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp [runResolvedFromTable]), one_mul]
      apply (add_le_add (hcharge input) htail).trans
      by_cases hquery : predicate input
      · have hpositive : 0 < bound := hbound.1.resolve_left (not_not.mpr hquery)
        cases bound with
        | zero => omega
        | succ bound => simp [remaining, hquery, Nat.cast_add, add_comm]
      · simp [remaining, hquery]

theorem expectedResolvedStructuralCharge_le_probeBound
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (bound : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound) :
    expectedResolvedQueryCharge structuralProbeQueryCharge computation context fuel table ≤ bound := by
  apply expectedResolvedQueryCharge_le_queryBound structuralProbeQueryCharge LazyRevealProbe.IsProbe _ computation bound context fuel table hbound
  intro input
  cases input <;> simp [structuralProbeQueryCharge, LazyRevealProbe.IsProbe]
  split <;> simp

theorem sum_targets_privateResolvedRawCandidate_hit_le_expectedStructuralCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcomplete : DeferredCompletable table context)
    (hensured : ∀ target ∈ targets, .position target ∈ context.state.ensured)
    (hstate : ∀ target ∈ targets, context.state.values (.position target) = none)
    (hvalue : ∀ target ∈ targets, context.values target = none)
    (hhidden : ∀ target ∈ targets, .position target ∉ context.state.revealed)
    (hcard : ∀ target ∈ targets, (context.state.pendingAt (.position target)).card + q ≤ 2 ^ 126) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table context fuel (privatePositionProbeCutAt target computation ordinal)]) ≤
      expectedResolvedQueryCharge structuralProbeQueryCharge computation context fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ ≤ ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[PrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)] *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
      apply Finset.sum_le_sum
      intro target htarget
      apply Finset.sum_le_sum
      intro ordinal hordinal
      apply probEvent_privateResolvedRawCandidate_hit_le_cut_reached target computation context fuel table ordinal hvalid hcomplete
        (hensured target htarget) (hstate target htarget) (hvalue target htarget) (hhidden target htarget)
      exact (Nat.add_le_add_left (Nat.le_of_lt (Finset.mem_range.mp hordinal)) _).trans (hcard target htarget)
    _ = (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[PrivateProbeCutReached target | runResolvedFromTable context fuel table (privatePositionProbeCutAt target computation ordinal)]) *
          ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul' (sum_targets_privateProbeCutReached_le_expectedStructuralCharge targets computation q context fuel table) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
